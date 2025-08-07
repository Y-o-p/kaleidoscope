#include <map>
#include <string>
#include <cstdio>
#include <variant>
#include <expected>
#include <vector>
#include <iostream>

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"

// LLVM specific globals
static std::unique_ptr<llvm::LLVMContext> TheContext;
static std::unique_ptr<llvm::IRBuilder<>> Builder;
static std::unique_ptr<llvm::Module> TheModule;
static std::map<std::string, llvm::Value *> NamedValues;


// Lexer
enum Token {
  tok_eof = -1,
  tok_def = -2,
  tok_extern = -3,
  tok_identifier = -4,
  tok_number = -5,
};

static std::string IdentifierStr;
static double NumVal;

static int gettok() {
  static int LastChar = ' ';
  while (isspace(LastChar)) {
    LastChar = getchar();
  }

  // Identifiers and commands (alphanumerics)
  if (isalpha(LastChar)) {
    // First letter of the identifier token is saved
    IdentifierStr = LastChar;

    // Build up the whole identifier token
    while (isalnum((LastChar = getchar()))) {
      IdentifierStr += LastChar;
    }

    // Evaluating the token
    if (IdentifierStr == "def") {
      //1printf(" 'def' ");
      return tok_def;
    }
    else if (IdentifierStr == "extern") {
      //printf(" 'extern' ");
      return tok_extern;
    }
    //std::cout << " 'identifier' ";
    return tok_identifier;
  }

  // Digits
  if (isdigit(LastChar) || LastChar == '.') {
    std::string NumStr;
    do {
      NumStr += LastChar;
      LastChar = getchar();
    } while (isdigit(LastChar) || LastChar == '.');

    NumVal = strtod(NumStr.c_str(), nullptr);
    //std::cout << " '" << NumVal << "' ";
    return tok_number;
  }

  // Comments
  if (LastChar == '#') {
    do {
      LastChar = getchar();
    } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

    if (LastChar != EOF) {
      return gettok();
    }
  }

  if (LastChar == EOF) {
    //printf(" 'EOF' ");
    return tok_eof;
  }

  int ThisChar = LastChar;
//  std::cout << " " << static_cast<char>(ThisChar) << " ";
  LastChar = getchar();
  return ThisChar;
}


static int CurTok;
static int getNextToken() {
  CurTok = gettok();
  return CurTok;
}


///////////////////////////////////////////////////////////////////////////////
/// Defining our expressions
///////////////////////////////////////////////////////////////////////////////

using Number = double;
using Variable = std::string;
struct BinaryExpression;
struct CallExpression;

using Expression = std::variant<Number, Variable, BinaryExpression*, CallExpression*>;
using MaybeExpression = std::expected<Expression, std::string>;

struct BinaryExpression {
  char Op;
  Expression LHS, RHS;
};

struct CallExpression {
  std::string Callee;
  std::vector<Expression> Args;
};

struct PrototypeAST {
  std::string Name;
  std::vector<std::string> Args;
};

using MaybePrototype = std::expected<PrototypeAST, std::string>;

struct FunctionAST {
  PrototypeAST Proto;
  Expression Body;
};

using MaybeFunction = std::expected<FunctionAST, std::string>;

///////////////////////////////////////////////////////////////////////////////
/// LLVM code generation
///////////////////////////////////////////////////////////////////////////////

static void GenerateCode(const Expression& AnyExpression) {
  std::visit([](auto&& Expr) {
    using T = std::decay_t<decltype(Expr)>;
    if constexpr (std::is_same_v<T, Number>) {
      std::cout << "It's a Number: " << Expr << std::endl;
    }
    else if constexpr (std::is_same_v<T, Variable>) {
      std::cout << "It's a Variable: " << Expr << std::endl;
    }
    else if constexpr (std::is_same_v<T, BinaryExpression*>) {
      std::cout << "It's a BinaryExpression: " << Expr->Op << std::endl;
    }
    else if constexpr (std::is_same_v<T, CallExpression*>) {
      std::cout << "It's a CallExpression: " << Expr->Callee << std::endl;
    }
  }, AnyExpression);
}

///////////////////////////////////////////////////////////////////////////////
/// PARSERS
///////////////////////////////////////////////////////////////////////////////

static Number ParseNumberExpr() {
  Number result = NumVal;
  getNextToken();
  return result;
}

static MaybeExpression ParseExpression();
static MaybeExpression ParseParenExpr() {
  getNextToken();
  MaybeExpression expr = ParseExpression();
  if (!expr.has_value()) {
    return expr;
  }

  if (CurTok != ')') {
    return std::unexpected("Expected a closing ).");
  }

  getNextToken();
  return expr;
}

static MaybeExpression ParseIdentifierExpr() {
  std::string IdName = IdentifierStr;
  getNextToken();

  if (CurTok != '(') {
    return Expression{Variable{IdName}};
  }

  // Eat the opening '('
  getNextToken();
  // Function call
  std::vector<Expression> Args;
  while (CurTok != ')') {
    MaybeExpression Arg = ParseExpression();
    if (Arg.has_value()) {
      Args.push_back(Arg.value());
    }
    else {
      return Arg;
    }

    if (CurTok == ')') {
      break;
    }

    if (CurTok != ',') {
      return std::unexpected("Expected ')' or ',' in argument list");
    }

    getNextToken();
  }

  // Eats the closing ')'
  getNextToken();

  return Expression{new CallExpression{IdName, Args}};
}

static MaybeExpression ParsePrimary() {
  switch (CurTok) {
    default:
      return std::unexpected("Unknown token. Expected expression.");
    case tok_identifier:
      return ParseIdentifierExpr();
    case tok_number:
      return Expression{ParseNumberExpr()};
    case '(':
      return ParseParenExpr();
  }
}

///////////////////////////////////////////////////////////////////////////////
/// Binary Operation Precedence
///////////////////////////////////////////////////////////////////////////////

static std::map<char, int> BinopPrecendence{
  {'<', 10},
  {'+', 20},
  {'-', 20},
  {'*', 40},
};

static int GetTokPrecendence() {
  if (!isascii(CurTok)) {
    return -1;
  }

  int TokPrec = BinopPrecendence[CurTok];
  if (TokPrec <= 0) {
    return -1;
  }

  return TokPrec;
}

static MaybeExpression ParseBinOpRHS(int ExprPrec, Expression LHS) {
  do {
    int TokPrec = GetTokPrecendence();

    if (TokPrec < ExprPrec) {
      return LHS;
    }

    int BinOp = CurTok;
    getNextToken();

    MaybeExpression RHS = ParsePrimary();
    if (!RHS.has_value()) {
      return RHS;
    }

    int NextPrec = GetTokPrecendence();
    if (TokPrec < NextPrec) {
      RHS = ParseBinOpRHS(TokPrec+1, RHS.value());
      if (!RHS.has_value()) {
        return RHS;
      }
    }

    LHS = new BinaryExpression{BinOp, LHS, RHS.value()};
  } while (true);
}


static MaybeExpression ParseExpression() {
  MaybeExpression LHS = ParsePrimary();
  if (!LHS.has_value()) {
    return LHS;
  }

  return ParseBinOpRHS(0, LHS.value());
}

///////////////////////////////////////////////////////////////////////////////
/// Other parsers
///////////////////////////////////////////////////////////////////////////////

static MaybePrototype ParsePrototype() {
  if (CurTok != tok_identifier) {
    return std::unexpected("Expected function name in prototype.");
  }

  std::string FnName = IdentifierStr;
  getNextToken();

  if (CurTok != '(') {
    return std::unexpected("Expected '(' in prototype.");
  }

  std::vector<std::string> ArgNames;
  while (getNextToken() == tok_identifier) {
    ArgNames.push_back(IdentifierStr);
  }
  if (CurTok != ')') {
    return std::unexpected("Expected ')' in prototype.");
  }

  // Success
  getNextToken();

  return PrototypeAST{FnName, ArgNames};
}

static MaybeFunction ParseDefinition() {
  getNextToken();
  auto Proto = ParsePrototype();
  if (!Proto.has_value()) {
    return std::unexpected(Proto.error());
  }

  auto Expr = ParseExpression();
  if (Expr.has_value()) {
    return FunctionAST{Proto.value(), Expr.value()};
  }
  return std::unexpected(Expr.error());
}

static MaybePrototype ParseExtern() {
  // Eat "extern"
  getNextToken();

  return ParsePrototype();
}

static MaybeFunction ParseTopLevelExpr() {
  MaybeExpression Expr = ParseExpression();
  if (Expr.has_value()) {
    auto Proto = PrototypeAST{"__anon_expr", {}};
    return FunctionAST{Proto, Expr.value()};
  }
  return std::unexpected(Expr.error());
}

template <typename F>
void Handle(F func, std::string success) {
  auto result = func();
  if (result.has_value()) {
    fprintf(stderr, "Parsed: %s\n", success.c_str());
  }
  else {
    fprintf(stderr, "Error: %s\n", result.error().c_str());
    getNextToken();
  }
}

int main() {
  getNextToken();
  while (CurTok != tok_eof) {
    switch (CurTok) {
      case ';':
        getNextToken();
        break;
      case tok_def:
        Handle(ParseDefinition, "definition");
        break;
      case tok_extern:
        Handle(ParseExtern, "extern");
        break;
      default:
        Handle(ParseTopLevelExpr, "top level expression");
        break;
    }
  }

  return 0;
}
