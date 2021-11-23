#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <queue>
#include <string.h>
#include <string>
#include <system_error>
#include <utility>
#include <vector>
#include "include/LinkedTable.h"

using namespace llvm;
using namespace llvm::sys;

FILE *pFile;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns one of these for known things.
enum TOKEN_TYPE
{

	IDENT = -1,		   // [a-zA-Z_][a-zA-Z_0-9]*
	ASSIGN = int('='), // '='

	// delimiters
	LBRA = int('{'),  // left brace
	RBRA = int('}'),  // right brace
	LPAR = int('('),  // left parenthesis
	RPAR = int(')'),  // right parenthesis
	SC = int(';'),	  // semicolon
	COMMA = int(','), // comma

	// types
	INT_TOK = -2,	// "int"
	VOID_TOK = -3,	// "void"
	FLOAT_TOK = -4, // "float"
	BOOL_TOK = -5,	// "bool"

	// keywords
	EXTERN = -6,  // "extern"
	IF = -7,	  // "if"
	ELSE = -8,	  // "else"
	WHILE = -9,	  // "while"
	RETURN = -10, // "return"
	// TRUE   = -12,     // "true"
	// FALSE   = -13,     // "false"

	// literals
	INT_LIT = -14,	 // [0-9]+
	FLOAT_LIT = -15, // [0-9]+.[0-9]+
	BOOL_LIT = -16,	 // "true" or "false" key words

	// logical operators
	AND = -17, // "&&"
	OR = -18,  // "||"

	// operators
	PLUS = int('+'),	// addition or unary plus
	MINUS = int('-'),	// substraction or unary negative
	ASTERIX = int('*'), // multiplication
	DIV = int('/'),		// division
	MOD = int('%'),		// modular
	NOT = int('!'),		// unary negation

	// comparison operators
	EQ = -19,	   // equal
	NE = -20,	   // not equal
	LE = -21,	   // less than or equal to
	LT = int('<'), // less than
	GE = -23,	   // greater than or equal to
	GT = int('>'), // greater than

	// special tokens
	EOF_TOK = 0, // signal end of file

	// invalid
	INVALID = -100 // signal invalid token
};

// TOKEN struct is used to keep track of information about a token
struct TOKEN
{
	int type = -100;
	std::string lexeme;
	int lineNo;
	int columnNo;
};

static std::string IdentifierStr; // Filled in if IDENT
static int IntVal;				  // Filled in if INT_LIT
static bool BoolVal;			  // Filled in if BOOL_LIT
static float FloatVal;			  // Filled in if FLOAT_LIT
static std::string StringVal;	  // Filled in if String Literal
static int lineNo, columnNo;

static TOKEN returnTok(std::string lexVal, int tok_type)
{
	TOKEN return_tok;
	return_tok.lexeme = lexVal;
	return_tok.type = tok_type;
	return_tok.lineNo = lineNo;
	return_tok.columnNo = columnNo - lexVal.length() - 1;
	return return_tok;
}

// Read file line by line -- or look for \n and if found add 1 to line number
// and reset column number to 0
/// gettok - Return the next token from standard input.
static TOKEN gettok()
{

	static int LastChar = ' ';
	static int NextChar = ' ';

	// Skip any whitespace.
	while (isspace(LastChar))
	{
		if (LastChar == '\n' || LastChar == '\r')
		{
			lineNo++;
			columnNo = 1;
		}
		LastChar = getc(pFile);
		columnNo++;
	}

	if (isalpha(LastChar) ||
		(LastChar == '_'))
	{ // identifier: [a-zA-Z_][a-zA-Z_0-9]*
		IdentifierStr = LastChar;
		columnNo++;

		while (isalnum((LastChar = getc(pFile))) || (LastChar == '_'))
		{
			IdentifierStr += LastChar;
			columnNo++;
		}

		if (IdentifierStr == "int")
			return returnTok("int", INT_TOK);
		if (IdentifierStr == "bool")
			return returnTok("bool", BOOL_TOK);
		if (IdentifierStr == "float")
			return returnTok("float", FLOAT_TOK);
		if (IdentifierStr == "void")
			return returnTok("void", VOID_TOK);
		if (IdentifierStr == "bool")
			return returnTok("bool", BOOL_TOK);
		if (IdentifierStr == "extern")
			return returnTok("extern", EXTERN);
		if (IdentifierStr == "if")
			return returnTok("if", IF);
		if (IdentifierStr == "else")
			return returnTok("else", ELSE);
		if (IdentifierStr == "while")
			return returnTok("while", WHILE);
		if (IdentifierStr == "return")
			return returnTok("return", RETURN);
		if (IdentifierStr == "true")
		{
			BoolVal = true;
			return returnTok("true", BOOL_LIT);
		}
		if (IdentifierStr == "false")
		{
			BoolVal = false;
			return returnTok("false", BOOL_LIT);
		}

		return returnTok(IdentifierStr.c_str(), IDENT);
	}

	if (LastChar == '=')
	{
		NextChar = getc(pFile);
		if (NextChar == '=')
		{ // EQ: ==
			LastChar = getc(pFile);
			columnNo += 2;
			return returnTok("==", EQ);
		}
		else
		{
			LastChar = NextChar;
			columnNo++;
			return returnTok("=", ASSIGN);
		}
	}

	if (LastChar == '{')
	{
		LastChar = getc(pFile);
		columnNo++;
		return returnTok("{", LBRA);
	}
	if (LastChar == '}')
	{
		LastChar = getc(pFile);
		columnNo++;
		return returnTok("}", RBRA);
	}
	if (LastChar == '(')
	{
		LastChar = getc(pFile);
		columnNo++;
		return returnTok("(", LPAR);
	}
	if (LastChar == ')')
	{
		LastChar = getc(pFile);
		columnNo++;
		return returnTok(")", RPAR);
	}
	if (LastChar == ';')
	{
		LastChar = getc(pFile);
		columnNo++;
		return returnTok(";", SC);
	}
	if (LastChar == ',')
	{
		LastChar = getc(pFile);
		columnNo++;
		return returnTok(",", COMMA);
	}

	if (isdigit(LastChar) || LastChar == '.')
	{ // Number: [0-9]+.
		std::string NumStr;

		if (LastChar == '.')
		{ // Floatingpoint Number: .[0-9]+
			do
			{
				NumStr += LastChar;
				LastChar = getc(pFile);
				columnNo++;
			} while (isdigit(LastChar));

			FloatVal = strtof(NumStr.c_str(), nullptr);
			return returnTok(NumStr, FLOAT_LIT);
		}
		else
		{
			do
			{ // Start of Number: [0-9]+
				NumStr += LastChar;
				LastChar = getc(pFile);
				columnNo++;
			} while (isdigit(LastChar));

			if (LastChar == '.')
			{ // Floatingpoint Number: [0-9]+.[0-9]+)
				do
				{
					NumStr += LastChar;
					LastChar = getc(pFile);
					columnNo++;
				} while (isdigit(LastChar));

				FloatVal = strtof(NumStr.c_str(), nullptr);
				return returnTok(NumStr, FLOAT_LIT);
			}
			else
			{ // Integer : [0-9]+
				IntVal = strtod(NumStr.c_str(), nullptr);
				return returnTok(NumStr, INT_LIT);
			}
		}
	}

	if (LastChar == '&')
	{
		NextChar = getc(pFile);
		if (NextChar == '&')
		{ // AND: &&
			LastChar = getc(pFile);
			columnNo += 2;
			return returnTok("&&", AND);
		}
		else
		{
			LastChar = NextChar;
			columnNo++;
			return returnTok("&", int('&'));
		}
	}

	if (LastChar == '|')
	{
		NextChar = getc(pFile);
		if (NextChar == '|')
		{ // OR: ||
			LastChar = getc(pFile);
			columnNo += 2;
			return returnTok("||", OR);
		}
		else
		{
			LastChar = NextChar;
			columnNo++;
			return returnTok("|", int('|'));
		}
	}

	if (LastChar == '!')
	{
		NextChar = getc(pFile);
		if (NextChar == '=')
		{ // NE: !=
			LastChar = getc(pFile);
			columnNo += 2;
			return returnTok("!=", NE);
		}
		else
		{
			LastChar = NextChar;
			columnNo++;
			return returnTok("!", NOT);
			;
		}
	}

	if (LastChar == '<')
	{
		NextChar = getc(pFile);
		if (NextChar == '=')
		{ // LE: <=
			LastChar = getc(pFile);
			columnNo += 2;
			return returnTok("<=", LE);
		}
		else
		{
			LastChar = NextChar;
			columnNo++;
			return returnTok("<", LT);
		}
	}

	if (LastChar == '>')
	{
		NextChar = getc(pFile);
		if (NextChar == '=')
		{ // GE: >=
			LastChar = getc(pFile);
			columnNo += 2;
			return returnTok(">=", GE);
		}
		else
		{
			LastChar = NextChar;
			columnNo++;
			return returnTok(">", GT);
		}
	}

	if (LastChar == '/')
	{ // could be division or could be the start of a comment
		LastChar = getc(pFile);
		columnNo++;
		if (LastChar == '/')
		{ // definitely a comment
			do
			{
				LastChar = getc(pFile);
				columnNo++;
			} while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

			if (LastChar != EOF)
				return gettok();
		}
		else
			return returnTok("/", DIV);
	}

	// Check for end of file.  Don't eat the EOF.
	if (LastChar == EOF)
	{
		columnNo++;
		return returnTok("0", EOF_TOK);
	}

	// Otherwise, just return the character as its ascii value.
	int ThisChar = LastChar;
	std::string s(1, ThisChar);
	LastChar = getc(pFile);
	columnNo++;
	return returnTok(s, int(ThisChar));
}

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static TOKEN CurTok;
static std::deque<TOKEN> tok_buffer;

static TOKEN getNextToken()
{

	if (tok_buffer.size() == 0)
		tok_buffer.push_back(gettok());

	TOKEN temp = tok_buffer.front();
	tok_buffer.pop_front();

	return CurTok = temp;
}

static void putBackToken(TOKEN tok) { tok_buffer.push_front(tok); }

//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

/// ASTnode - Base class for all AST nodes.
class ASTnode
{
public:
	virtual ~ASTnode() {}
	virtual Value *codegen() = 0;
	virtual std::string to_string() const {};
};

//ASTnode to hold the IDENT
//Contains a string and the token
class IDENTIFICATOR : public ASTnode
{

	TOKEN Tok;
	std::string Name;

public:
	IDENTIFICATOR(std::string name, TOKEN tok)
	{
		Name = std::move(name);
		Tok = std::move(tok);
	}

	std::string getVarName()
	{
		return Name;
	}

	TOKEN getVarToken()
	{
		return Tok;
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		return "[ID]: " + Name;
	}
};

//ASTnode to hold the FunctionParameter
//Holds the param type and the name
class Param : public ASTnode
{

public:
	std::string VarType;
	std::unique_ptr<IDENTIFICATOR> ID;

	Param(std::string varType, std::unique_ptr<IDENTIFICATOR> id)
	{
		VarType = varType;
		ID = std::move(id);
	}

	std::string getType()
	{
		return VarType;
	}

	std::string getName()
	{
		return ID->getVarName();
	}

	virtual Value *codegen() override{};

	virtual std::string to_string() const override
	{
		return "[" + VarType + " " + ID->to_string() + "]";
	}
};

//ASTnode that holds the params of a function definition
//has an array of parameters and the word "void", if the function has void param
class Params : public ASTnode
{

public:
	std::vector<std::unique_ptr<Param>> _ParameterList_;
	std::string VoidTok;

	Params(std::vector<std::unique_ptr<Param>> _param, std::string voidtok)
	{
		_ParameterList_ = std::move(_param);
		VoidTok = voidtok;
	}

	std::string getVoidTok()
	{
		return VoidTok;
	}

	std::vector<std::unique_ptr<Param>> getParams()
	{
		return std::move(_ParameterList_);
	}

	std::unique_ptr<Param> getParam(int pos)
	{
		return std::move(_ParameterList_[pos]);
	}

	virtual Value *codegen() override{};

	virtual std::string to_string() const override
	{
		std::string s = "[Params]: ";

		if (VoidTok != "")
			s = s + VoidTok;
		else
		{
			if (_ParameterList_.size() == 0)
			{
				s = s + "-";
			}
			else
			{
				for (int i = 0; i < _ParameterList_.size() - 1; i++)
				{
					s = s + _ParameterList_[i]->to_string() + ", ";
				}
				s = s + _ParameterList_[_ParameterList_.size() - 1]->to_string();
			}
		}

		return s;
	}
};

//ASTnode to hold int literals
class IntLit : public ASTnode
{
	int Val;
	TOKEN Tok;
	std::string Name;

public:
	IntLit(TOKEN tok, int val, std::string name)
	{
		Val = val;
		Name = name;
		Tok = tok;
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		return "<Int>" + std::to_string(Val);
	}
};

//ASTnode to hold the Float literals
class FloatLit : public ASTnode
{
	float Val;
	TOKEN Tok;
	std::string Name;

public:
	FloatLit(TOKEN tok, float val, std::string name)
	{
		Val = val;
		Name = name;
		Tok = tok;
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		return "<Float>" + std::to_string(Val);
	}
};

//ASTnode to hold the Boolean literals
class BoolLit : public ASTnode
{
	bool Val;
	TOKEN Tok;
	std::string Name;

public:
	BoolLit(TOKEN tok, bool val, std::string name)
	{
		Val = val;
		Name = name;
		Tok = tok;
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		return "<Bool>" + std::to_string(Val);
	}
};

//ASTnode to hold the function arguments.
//Contains an array of parameters, each being an expr
class FunctionArgs : public ASTnode
{

public:
	std::vector<std::unique_ptr<ASTnode>> ArgumentsArr;

	FunctionArgs(std::vector<std::unique_ptr<ASTnode>> args)
	{
		ArgumentsArr = std::move(args);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		for (int i = 0; i < ArgumentsArr.size() - 1; i++)
		{
			return ArgumentsArr[i]->to_string() + ", ";
		}

		return ArgumentsArr[ArgumentsArr.size() - 1]->to_string();
	}
};

//ASTnode to hold the function call
//Contains the name of the function to be called and the arguments
class FunctionCall : public ASTnode
{

	std::unique_ptr<IDENTIFICATOR> ID;
	std::unique_ptr<FunctionArgs> Args;

public:
	FunctionCall(std::unique_ptr<IDENTIFICATOR> id, std::unique_ptr<FunctionArgs> args)
	{
		ID = std::move(id);
		Args = std::move(args);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		return "[FunctionCall]: " + ID->to_string() + "(" + Args->to_string() + ")";
	}
};

//ASTnode to hold the Element production -> see gramar for references
class Element : public ASTnode
{

	std::unique_ptr<IDENTIFICATOR> ID;
	std::unique_ptr<ASTnode> FunctionCall_s;
	std::unique_ptr<ASTnode> Expression;
	std::unique_ptr<ASTnode> Literal;

public:
	Element(std::unique_ptr<IDENTIFICATOR> id, std::unique_ptr<ASTnode> expr, std::unique_ptr<ASTnode> call, std::unique_ptr<ASTnode> literal)
	{
		ID = std::move(id);
		FunctionCall_s = std::move(call);
		Expression = std::move(expr);
		Literal = std::move(literal);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[ELEMENT Node]";
		if (Expression)
		{
			s = s + Expression->to_string();
		}
		else if (FunctionCall_s)
		{
			s = s + FunctionCall_s->to_string();
		}
		else if (ID)
		{
			s = s + " " + ID->to_string();
		}
		else if (Literal)
		{
			s = s + " " + Literal->to_string();
		}
		return s;
	}
};

//ASTnode to hold the Unary production -> see gramar for references
class UnaryOp : public ASTnode
{

	std::unique_ptr<ASTnode> EXPR;
	int OP;

public:
	UnaryOp(int op, std::unique_ptr<ASTnode> expr)
	{
		OP = op;
		EXPR = std::move(expr);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		if (OP != INVALID)
			return "([Unary Node]: " + std::to_string(OP) + EXPR->to_string() + ")";
		else
			return "([Unary Node]: " + EXPR->to_string() + ")";
	}
};

//ASTnode to hold the BinOp.
//Contains the left operation, the operator and the right operation
class BinOp : public ASTnode
{
	std::unique_ptr<ASTnode> Left;
	std::unique_ptr<ASTnode> Right;
	int OP;

public:
	BinOp(std::unique_ptr<ASTnode> left, std::unique_ptr<ASTnode> right, int op)
	{
		Left = std::move(left);
		Right = std::move(right);
		OP = op;
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[BinOp Node]: [";

		return Left->to_string() + " " + std::to_string(OP) + " " + Right->to_string() + "]\n";
	}
};

//ASTnode to hold an expression production -> see gramar for references
class EXPR : public ASTnode
{
	std::unique_ptr<IDENTIFICATOR> ID;
	std::unique_ptr<ASTnode> BinOPERATOR;

public:
	EXPR(std::unique_ptr<IDENTIFICATOR> id, std::unique_ptr<ASTnode> binOP)
	{
		ID = std::move(id);
		BinOPERATOR = std::move(binOP);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[EXPR Node] [\n ";

		if (ID)
			s = s + ID->to_string() + " <> ";
		if (BinOPERATOR)
			s = s + BinOPERATOR->to_string();
		return s + "]";
	}
};

//ASTnode to hold an row
//Conains aither and expression, nor a bool var that is true, when it is only a semicolon per row
class EXPR_STMT : public ASTnode
{
	std::unique_ptr<ASTnode> Expression;
	bool isSemicolonOnly;

public:
	EXPR_STMT(std::unique_ptr<ASTnode> expression, bool isSemicolon)
	{
		Expression = std::move(expression);
		isSemicolonOnly = isSemicolon;
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[EXPR_STMT Node]\n";

		if (isSemicolonOnly)
		{
			s = s + ";";
		}
		else
		{
			if (Expression)
				s = s + Expression->to_string() + "\n";
		}
		return s;
	}
};

//ASTnode for the Return production -> see gramar for references
class RETURN_STMT : public ASTnode
{
	bool NoExpr;
	std::unique_ptr<ASTnode> Expression;
	TOKEN Tok;

public:
	RETURN_STMT(bool noExpr, std::unique_ptr<ASTnode> expression, TOKEN tok)
	{
		NoExpr = noExpr;
		Expression = std::move(expression);
		Tok = tok;
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[RETURN Node] \n";

		if (NoExpr)
		{
			s = s + ";";
		}
		else
		{
			s = s + Expression->to_string() + "\n";
		}
		return s;
	}
};

//ASTnode for the WHILE production -> see gramar for references
class WHILE_STMT : public ASTnode
{
	std::unique_ptr<ASTnode> Expression;
	std::unique_ptr<ASTnode> STMT_s;

public:
	WHILE_STMT(std::unique_ptr<ASTnode> expression, std::unique_ptr<ASTnode> stmt)
	{
		Expression = std::move(expression);
		STMT_s = std::move(stmt);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[WHILE STMT Node] \n";

		s = s + "<" + Expression->to_string() + ">" + "\n";
		if (STMT_s)
		{
			// s = "[STATEMENTS]\n";
			s = s + STMT_s->to_string();
		}

		return s + "\n";
	}
};

//ASTnode for the IF production -> see gramar for references
class IF_STMT : public ASTnode
{
	std::unique_ptr<ASTnode> Expression;
	std::unique_ptr<ASTnode> Block_TRUE_s;
	std::unique_ptr<ASTnode> Block_FALSE;

public:
	IF_STMT(std::unique_ptr<ASTnode> expression, std::unique_ptr<ASTnode> block_true, std::unique_ptr<ASTnode> block_false)
	{
		Expression = std::move(expression);
		Block_TRUE_s = std::move(block_true);
		Block_FALSE = std::move(block_false);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[IF STMT Node] \n";

		if (Expression)
			s = s + "<" + Expression->to_string() + ">" + "\n";

		if (Block_TRUE_s)
		{
			s = s + "[True Block]\n";
			// s = s + Block_TRUE_s->to_string() + "\n";
		}

		if (Block_FALSE)
		{
			s = s + "[False Block]";
			// s = s + Block_FALSE->to_string();
		}

		return s;
	}
};

//ASTnode for the STMT production -> see gramar for references
class STMT : public ASTnode
{
	std::unique_ptr<ASTnode> EXPR_s;
	std::unique_ptr<ASTnode> Block_s;
	std::unique_ptr<ASTnode> IF_s;
	std::unique_ptr<ASTnode> WHILE_s;
	std::unique_ptr<ASTnode> RETURN_s;

public:
	STMT(
		std::unique_ptr<ASTnode> expr,
		std::unique_ptr<ASTnode> block,
		std::unique_ptr<ASTnode> if_b,
		std::unique_ptr<ASTnode> while_b,
		std::unique_ptr<ASTnode> return_b)
	{
		EXPR_s = std::move(expr);
		Block_s = std::move(block);
		IF_s = std::move(if_b);
		WHILE_s = std::move(while_b);
		RETURN_s = std::move(return_b);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "";

		if (EXPR_s)
		{
			s = s + EXPR_s->to_string();
			return s;
		}
		if (Block_s)
		{
			return Block_s->to_string();
		}
		if (IF_s)
		{
			return IF_s->to_string();
		}
		if (WHILE_s)
		{
			return WHILE_s->to_string();
		}
		if (RETURN_s)
		{
			return RETURN_s->to_string();
		}

		return "";
	}
};

//ASTnode for the STMT list
//Contains an array of STMTs
class STMTlist : public ASTnode
{
	std::vector<std::unique_ptr<ASTnode>> STMT;

public:
	STMTlist(std::vector<std::unique_ptr<ASTnode>> stmt)
	{
		STMT = std::move(stmt);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[STMT_List block] \n";

		for (int i = 0; i < STMT.size() - 1; i++)
		{
			s = s + STMT[i]->to_string() + "\n";
		}

		s = s + STMT[STMT.size() - 1]->to_string() + "\n";

		return s;
	}
};

//ASTnode for the local variable decaration
//Contains its type and name
class LocalDeclaration : public ASTnode
{
	std::string VarType;
	std::unique_ptr<IDENTIFICATOR> ID;

public:
	LocalDeclaration(std::string varType, std::unique_ptr<IDENTIFICATOR> id)
	{
		VarType = varType;
		ID = std::move(id);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		return VarType + " " + ID->to_string();
	}
};

//ASTnode to hold the local declarations
//Contains and array
class LocalDeclarations : public ASTnode
{
	std::vector<std::unique_ptr<ASTnode>> LocalDeclaration;

public:
	LocalDeclarations(std::vector<std::unique_ptr<ASTnode>> localDeclaration)
	{
		LocalDeclaration = std::move(localDeclaration);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[LocalDeclarations] \n";

		for (int i = 0; i < LocalDeclaration.size() - 1; i++)
		{
			s = s + LocalDeclaration[i]->to_string() + ", ";
		}

		s = s + LocalDeclaration[LocalDeclaration.size() - 1]->to_string() + "\n";

		return s;
	}
};

//ASTnode to hold a block of instructions
//Contains a local delcaration and STMT list pointer.
//if one or both are nonexistent, then they are nullptr
class Block : public ASTnode
{
	std::unique_ptr<ASTnode> LocalDeclarations;
	std::unique_ptr<ASTnode> STMTlist;

public:
	Block(std::unique_ptr<ASTnode> localDeclarations, std::unique_ptr<ASTnode> stmtList)
	{
		LocalDeclarations = std::move(localDeclarations);
		STMTlist = std::move(stmtList);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		if (STMTlist != nullptr)
		{
			std::string s = "[Block] \n";

			if (LocalDeclarations)
				s = s + LocalDeclarations->to_string();
			if (STMTlist)
				s = s + STMTlist->to_string();
			return s;
		}
		return "";
	}
};

//ASTnode for global var delcaration
//Contains a variable type and its name
class VariableDeclaration : public ASTnode
{
	std::string VarType;
	std::unique_ptr<IDENTIFICATOR> ID;

public:
	VariableDeclaration(std::string type, std::unique_ptr<IDENTIFICATOR> id)
	{
		ID = std::move(id);
		VarType = type;
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		return VarType + " " + ID->to_string();
	}
};

//ASTnode for function delcaration
//Contains its siganture, name, params and block
class FunctionDeclaration : public ASTnode
{
	std::string TypeSpec;
	std::unique_ptr<IDENTIFICATOR> ID;
	std::unique_ptr<Params> _Params;
	std::unique_ptr<ASTnode> Block;

public:
	FunctionDeclaration(std::string typeSpec, std::unique_ptr<IDENTIFICATOR> id, std::unique_ptr<Params> __params, std::unique_ptr<ASTnode> block)
	{
		TypeSpec = typeSpec;
		ID = std::move(id);
		_Params = std::move(__params);
		Block = std::move(block);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "";

		s = s + TypeSpec + " " + ID->to_string() + " (" + _Params->to_string() + ") \n";
		if (Block)
			s = s + Block->to_string();
		return s;
	}
};

//ASTnode selector
//Can contains both, one or none of the global declaration and function declaration
class Declaration : public ASTnode
{

	std::unique_ptr<ASTnode> VariableDeclaration;
	std::unique_ptr<ASTnode> FunctionDeclaration;

public:
	Declaration(std::unique_ptr<ASTnode> varDecl, std::unique_ptr<ASTnode> funcDecl)
	{
		VariableDeclaration = std::move(varDecl);
		FunctionDeclaration = std::move(funcDecl);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "";

		if (VariableDeclaration)
		{
			s = s + "[Variable Declaration]: \n";
			s = s + VariableDeclaration->to_string();
		}
		if (FunctionDeclaration)
		{
			s = s + "[Function Declaration]:\n";
			s = s + FunctionDeclaration->to_string();
		}

		return s;
	}
};

//ASTnode to hold a declaration list
//Contains an array of declarations
class DeclarationList : public ASTnode
{
	std::vector<std::unique_ptr<ASTnode>> Declarations;

public:
	DeclarationList(std::vector<std::unique_ptr<ASTnode>> declarations)
	{
		Declarations = std::move(declarations);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[DeclarationList Node]\n";
		if (Declarations.size() == 0)
		{
			s = s + "no declaration found";
		}
		else
		{
			for (int i = 0; i < Declarations.size(); i++)
			{
				s = s + Declarations[i]->to_string();
			}
		}
		return s;
	}
};

//ASTnode to contains an extern function declaration
class Extern : public ASTnode
{

	std::string TypeSpec;
	std::unique_ptr<IDENTIFICATOR> ID;
	std::unique_ptr<Params> _Params;

public:
	Extern(std::string typeSpec, std::unique_ptr<IDENTIFICATOR> id, std::unique_ptr<Params> __params)
	{
		TypeSpec = std::move(typeSpec);
		ID = std::move(id);
		_Params = std::move(__params);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "| [Extern Node]: [";

		s = s + TypeSpec + " <> " + ID->to_string() + " <> (" + _Params->to_string() + ")";

		s = s + "]\n";

		return s;
	}
};

//ASTnode to hold the extern fct declaration
//Contains an array of extern declarations
class ExternList : public ASTnode
{

	std::vector<std::unique_ptr<ASTnode>> Externs;

public:
	ExternList(std::vector<std::unique_ptr<ASTnode>> externs)
	{
		Externs = std::move(externs);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[ExternList Node]\n";

		for (int i = 0; i < Externs.size(); i++)
		{
			s = s + Externs[i]->to_string();
		}

		return s;
	}
};

//Root of the parser
class Program : public ASTnode
{

	std::unique_ptr<ASTnode> ExternList;
	std::unique_ptr<ASTnode> DeclarationList;

public:
	Program(std::unique_ptr<ASTnode> extern_list, std::unique_ptr<ASTnode> decl_list)
	{
		ExternList = std::move(extern_list);
		DeclarationList = std::move(decl_list);
	}

	virtual Value *codegen() override;

	virtual std::string to_string() const override
	{
		std::string s = "[Program Node]\n\n";

		if (ExternList)
			s = s + ExternList->to_string();

		if (DeclarationList)
			s = s + DeclarationList->to_string();

		return s + "[END Program Node]";
	}
};

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

/* Add function calls for each production */

/* The function names tells exactly what the function does.
 * There is no need to explain more: 
 * Checks if TOKEN in the first set: 
 * | if yes => the parse the rest,
 * | if no, check if TOKEN in follow set:
 * | | if yes, => go to the next production;
 * | | if no, => throw error;
 * - -
 */
/* ==== PROTOTYPES ==== */
static std::unique_ptr<IDENTIFICATOR> ParseID();
static std::unique_ptr<ASTnode> ParseBlock();
static std::unique_ptr<FunctionArgs> ParseArgs();
static std::unique_ptr<ASTnode> ParseElem();
static std::unique_ptr<ASTnode> ParseUnary();
static std::unique_ptr<ASTnode> ParseFactor_Prime(std::unique_ptr<ASTnode> unary);
static std::unique_ptr<ASTnode> ParseFactor();
static std::unique_ptr<ASTnode> ParseSubexpr_Prime(std::unique_ptr<ASTnode> factor);
static std::unique_ptr<ASTnode> ParseSubexpr();
static std::unique_ptr<ASTnode> ParseRel_Prime(std::unique_ptr<ASTnode> subexpr);
static std::unique_ptr<ASTnode> ParseRel();
static std::unique_ptr<ASTnode> ParseEquiv_Prime(std::unique_ptr<ASTnode> rel);
static std::unique_ptr<ASTnode> ParseEquiv();
static std::unique_ptr<ASTnode> ParseAND_Prime(std::unique_ptr<ASTnode> equiv);
static std::unique_ptr<ASTnode> ParseAND();
static std::unique_ptr<ASTnode> ParseOR_Prime(std::unique_ptr<ASTnode> AndOP);
static std::unique_ptr<ASTnode> ParseOR();
static std::unique_ptr<ASTnode> ParseExpr();
static std::unique_ptr<ASTnode> ParseReturn();
static std::unique_ptr<ASTnode> ParseWhile();
static std::unique_ptr<ASTnode> ParseElseStmt();
static std::unique_ptr<ASTnode> ParseIF();
static std::unique_ptr<ASTnode> ParseExprSTMT();
static std::unique_ptr<ASTnode> ParseStatement();
static std::unique_ptr<ASTnode> ParseStatementList();
static std::unique_ptr<ASTnode> ParseLocalDeclaration();
static std::unique_ptr<ASTnode> ParseLocalDeclarations();
static std::unique_ptr<Param> ParseParam();
static std::unique_ptr<Params> ParseParams();
static std::unique_ptr<ASTnode> ParseFunction(std::string type, std::unique_ptr<IDENTIFICATOR> ID);
static std::unique_ptr<ASTnode> ParseDeclaration();
static std::unique_ptr<ASTnode> ParseExtern();
static std::unique_ptr<ASTnode> ParseDeclList();
static std::unique_ptr<ASTnode> ParseExternList();
static std::unique_ptr<ASTnode> ParseProgram();
static std::unique_ptr<ASTnode> MainParserDriver();

/* ==== FUNCTIONS ==== */

//Function to report errors
static std::unique_ptr<ASTnode> reportError(std::string msg, TOKEN currTok)
{
	std::cout << "\033[31m" << "[Parsing Error] " << "\033[0m"; 
	std::cout << msg << " on line " << currTok.lineNo << ", col " << currTok.columnNo << ", but found " << currTok.lexeme << std::endl;
	return nullptr;
}

//Function to report ID errors
static std::unique_ptr<IDENTIFICATOR> reportErrID(std::string msg, TOKEN currTok)
{
	std::cout << "\033[31m" << "[Parsing Error] " << "\033[0m"; 
	std::cout << msg << " on line " << currTok.lineNo << ", col " << currTok.columnNo << ", but found " << currTok.lexeme << std::endl;
	return nullptr;
}

static std::unique_ptr<IDENTIFICATOR> ParseID()
{
	if (CurTok.type == IDENT)
	{
		std::string id = CurTok.lexeme;
		getNextToken();
		return std::move(
			std::make_unique<IDENTIFICATOR>(id, std::move(CurTok)));
	}
	else
		return reportErrID("Expected identificator", CurTok);
}

static std::unique_ptr<ASTnode> ParseBlock()
{
	if (CurTok.type == LBRA)
	{
		getNextToken();
		auto localDeclarations = ParseLocalDeclarations();
		if (localDeclarations)
		{

			auto stmtList = ParseStatementList();
			if (stmtList)
			{

				if (CurTok.type == RBRA)
				{

					getNextToken();
					return std::move(
						std::make_unique<Block>(
							std::move(localDeclarations), std::move(stmtList)));
				}
				else
					return reportError("Expected right bracket", CurTok);
			}
			else
				return nullptr;
		}
		else
			return nullptr;
	}
	else
		return reportError("Expected left bracket", CurTok);
}

static std::unique_ptr<FunctionArgs> ParseArgs()
{
	std::vector<std::unique_ptr<ASTnode>> args;

	getNextToken();
	if (CurTok.type == RPAR)
	{
		return std::move(std::make_unique<FunctionArgs>(std::move(args)));
	}

	while (CurTok.type == COMMA || CurTok.type == MINUS ||
		   CurTok.type == NOT || CurTok.type == LPAR ||
		   CurTok.type == IDENT || CurTok.type == INT_LIT ||
		   CurTok.type == FLOAT_LIT || CurTok.type == BOOL_LIT)
	{
		auto expr = ParseExpr();
		if (expr)
		{
			args.push_back(std::move(expr));

			if(CurTok.type == COMMA)
				getNextToken();
		}
		else
			return nullptr;
	}

	return std::move(
		std::make_unique<FunctionArgs>(std::move(args)));
}

static std::unique_ptr<ASTnode> ParseElem()
{
	if (CurTok.type == IDENT)
	{
		auto id = ParseID();
		//de pus if
		if (CurTok.type == LPAR)
		{
			auto args = ParseArgs();
			if (args)
			{
				if (CurTok.type == RPAR)
				{
					getNextToken();

					auto functionCall = std::move(
						std::make_unique<FunctionCall>(
							std::move(id),
							std::move(args)));

					return std::move(
						std::make_unique<Element>(
							nullptr,
							nullptr,
							std::move(functionCall),
							nullptr));
				}
				else
					return reportError("Expected right paranthesis", CurTok);
			}
			else
				return nullptr;
		}
		else
		{
			return std::move(
				std::make_unique<Element>(
					std::move(id),
					nullptr,
					nullptr,
					nullptr));
		}
	}
	else if (CurTok.type == LPAR)
	{
		getNextToken();
		auto expr = ParseExpr();
		if (expr)
		{
			if (CurTok.type == RPAR)
			{
				getNextToken();
				return std::move(
					std::make_unique<Element>(
						nullptr,
						std::move(expr),
						nullptr,
						nullptr));
			}
			else
				return reportError("Expected right paranthesis", CurTok);
		}
		else
			return nullptr;
	}
	else if (CurTok.type == INT_LIT)
	{
		auto intlit = std::make_unique<IntLit>(CurTok, std::stoi(CurTok.lexeme), "");
		getNextToken();
		return std::move(
			std::make_unique<Element>(
				nullptr,
				nullptr,
				nullptr,
				std::move(intlit)));
	}
	else if (CurTok.type == FLOAT_LIT)
	{
		auto floatlit = std::make_unique<FloatLit>(CurTok, std::stof(CurTok.lexeme), "");
		getNextToken();
		return std::move(
			std::make_unique<Element>(
				nullptr,
				nullptr,
				nullptr,
				std::move(floatlit)));
	}
	else if (CurTok.type == BOOL_LIT)
	{
		bool b;
		if (CurTok.lexeme == "true")
			b = true;
		else if (CurTok.lexeme == "false")
			b = false;
		else
			return reportError("Expected true or false", CurTok);

		auto boollit = std::make_unique<BoolLit>(CurTok, b, "");
		getNextToken();
		return std::move(
			std::make_unique<Element>(
				nullptr,
				nullptr,
				nullptr,
				std::move(boollit)));
	}
	else
		return reportError("Expected (, identificator, number or bool", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> ParseUnary()
{
	if (CurTok.type == MINUS || CurTok.type == NOT)
	{
		int curOperator = CurTok.type;
		getNextToken();
		auto unary = ParseUnary();
		if (unary)
		{
			return std::move(
				std::make_unique<UnaryOp>(
					curOperator,
					std::move(unary)));
		}
		else
			return nullptr;
	}
	else if (CurTok.type == LPAR || CurTok.type == IDENT ||
			 CurTok.type == FLOAT_LIT || CurTok.type == BOOL_LIT ||
			 CurTok.type == INT_LIT)
	{

		auto elem = ParseElem();
		if (elem)
		{
			return std::move(elem);
		}
	}
	else
		return reportError("Expected unary", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> ParseFactor_Prime(std::unique_ptr<ASTnode> unary)
{
	if (CurTok.type == ASTERIX || CurTok.type == DIV || CurTok.type == MOD)
	{
		int curOperator = CurTok.type;
		getNextToken();
		auto unary_2 = ParseUnary();
		if (unary_2)
		{
			auto binOP = std::make_unique<BinOp>(
				std::move(unary),
				std::move(unary_2),
				curOperator);
			return std::move(ParseFactor_Prime(std::move(binOP)));
		}
	}
	else if (CurTok.type == RPAR || CurTok.type == SC ||
			 CurTok.type == COMMA || CurTok.type == OR ||
			 CurTok.type == AND || CurTok.type == EQ ||
			 CurTok.type == NE || CurTok.type == LT ||
			 CurTok.type == LE || CurTok.type == GT ||
			 CurTok.type == GE || CurTok.type == PLUS ||
			 CurTok.type == MINUS)
	{
		return std::move(unary);
	}
	else
		return reportError("Expected *, /, % operator", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> ParseFactor()
{
	auto unary = ParseUnary();
	if (unary)
	{
		return std::move(
			ParseFactor_Prime(
				std::move(unary)));
	}
	else
		return nullptr;
}

static std::unique_ptr<ASTnode> ParseSubexpr_Prime(std::unique_ptr<ASTnode> factor)
{
	if (CurTok.type == PLUS || CurTok.type == MINUS)
	{
		int curOperator = CurTok.type;
		getNextToken();
		auto factor_2 = ParseFactor();
		if (factor_2)
		{
			auto binOP = std::make_unique<BinOp>(
				std::move(factor),
				std::move(factor_2),
				curOperator);
			return std::move(ParseSubexpr_Prime(std::move(binOP)));
		}
	}
	else if (CurTok.type == RPAR || CurTok.type == SC ||
			 CurTok.type == COMMA || CurTok.type == OR ||
			 CurTok.type == AND || CurTok.type == EQ ||
			 CurTok.type == NE || CurTok.type == LT ||
			 CurTok.type == LE || CurTok.type == GT ||
			 CurTok.type == GE)
	{
		return std::move(factor);
	}
	else
		return reportError("Expected + or - operator", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> ParseSubexpr()
{
	auto factor = ParseFactor();
	if (factor)
	{
		return std::move(
			ParseSubexpr_Prime(
				std::move(factor)));
	}
	else
		return nullptr;
}

static std::unique_ptr<ASTnode> ParseRel_Prime(std::unique_ptr<ASTnode> subexpr)
{
	if (CurTok.type == LT || CurTok.type == LE ||
		CurTok.type == GT || CurTok.type == GE)
	{
		int curOperator = CurTok.type;
		getNextToken();
		auto subexpr_2 = ParseSubexpr();
		if (subexpr_2)
		{
			auto binOP = std::make_unique<BinOp>(
				std::move(subexpr),
				std::move(subexpr_2),
				curOperator);
			return std::move(ParseRel_Prime(std::move(binOP)));
		}
	}
	else if (CurTok.type == RPAR || CurTok.type == SC ||
			 CurTok.type == COMMA || CurTok.type == OR ||
			 CurTok.type == AND || CurTok.type == EQ ||
			 CurTok.type == NE)
	{
		return std::move(subexpr);
	}
	else
		return reportError("Expected <, <=, >= or > operator", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> ParseRel()
{
	auto subexpr = ParseSubexpr();
	if (subexpr)
	{
		return std::move(
			ParseRel_Prime(
				std::move(subexpr)));
	}
	else
		return nullptr;
}

static std::unique_ptr<ASTnode> ParseEquiv_Prime(std::unique_ptr<ASTnode> rel)
{
	if (CurTok.type == EQ || CurTok.type == NE)
	{
		int curOperator = CurTok.type;
		getNextToken();
		auto rel_2 = ParseRel();
		if (rel_2)
		{
			auto binOP = std::make_unique<BinOp>(
				std::move(rel),
				std::move(rel_2),
				curOperator);
			return std::move(ParseEquiv_Prime(std::move(binOP)));
		}
	}
	else if (CurTok.type == RPAR || CurTok.type == SC ||
			 CurTok.type == COMMA || CurTok.type == OR ||
			 CurTok.type == AND)
	{
		return std::move(rel);
	}
	else
		return reportError("Expected != or = operator", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> ParseEquiv()
{
	auto rel = ParseRel();
	if (rel)
	{
		return std::move(
			ParseEquiv_Prime(
				std::move(rel)));
	}
	else
		return nullptr;
}

static std::unique_ptr<ASTnode> ParseAND_Prime(std::unique_ptr<ASTnode> equiv)
{
	if (CurTok.type == AND)
	{
		int curOperator = CurTok.type;
		getNextToken();
		auto equiv_2 = ParseEquiv();
		if (equiv_2)
		{
			auto binOP = std::make_unique<BinOp>(
				std::move(equiv),
				std::move(equiv_2),
				curOperator);
			return std::move(ParseAND_Prime(std::move(binOP)));
		}
	}
	else if (CurTok.type == RPAR || CurTok.type == SC ||
			 CurTok.type == COMMA || CurTok.type == OR)
	{
		return std::move(equiv);
	}
	else
		return reportError("Expected and operator", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> ParseAND()
{
	auto equiv = ParseEquiv();
	if (equiv)
	{
		return std::move(
			ParseAND_Prime(
				std::move(equiv)));
	}
	else
		return nullptr;
}

static std::unique_ptr<ASTnode> ParseOR_Prime(std::unique_ptr<ASTnode> AndOP)
{
	if (CurTok.type == OR)
	{
		int curOperator = CurTok.type;
		getNextToken();
		auto andOP_2 = ParseAND();
		if (andOP_2)
		{
			auto binOP = std::make_unique<BinOp>(
				std::move(AndOP),
				std::move(andOP_2),
				curOperator);
			return std::move(ParseOR_Prime(std::move(binOP)));
		}
	}
	else if (CurTok.type == RPAR || CurTok.type == SC || CurTok.type == COMMA)
	{
		return std::move(AndOP);
	}
	else
		return reportError("Expected or operator", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> ParseOR()
{

	auto andOP = ParseAND();
	if (andOP)
	{
		return std::move(
			ParseOR_Prime(
				std::move(andOP)));
	}
	else
		return nullptr;
}

static std::unique_ptr<ASTnode> ParseExpr()
{
	if (CurTok.type == IDENT)
	{
		TOKEN firstLook = CurTok;
		getNextToken();

		if (CurTok.type == ASSIGN)
		{
			putBackToken(CurTok);
			putBackToken(firstLook);
			getNextToken();
			auto id = ParseID();
			if (id)
			{
				getNextToken();
				auto expr = ParseExpr();
				if (expr)
				{
					return std::move(
						std::make_unique<EXPR>(
							std::move(id),
							std::move(expr)));
				}
				else
					return nullptr;
			}
		}
		else
		{
			putBackToken(CurTok);
			putBackToken(firstLook);
			getNextToken();
			auto or_expr = ParseOR();
			if (or_expr)
			{
				return std::move(
					std::make_unique<EXPR>(
						nullptr,
						std::move(or_expr)));
			}
		}
	}
	else if (CurTok.type == MINUS || CurTok.type == NOT ||
			 CurTok.type == INT_LIT || CurTok.type == FLOAT_LIT ||
			 CurTok.type == BOOL_LIT || CurTok.type == LPAR)
	{

		auto or_expr = ParseOR();
		if (or_expr)
		{
			return std::move(
				std::make_unique<EXPR>(
					nullptr,
					std::move(or_expr)));
		}
		else
			return nullptr;
	}
	else
		return reportError("Expected identificator or minus, not, int var, float var or bool var", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> ParseReturn()
{
	if (CurTok.type == RETURN)
	{

		getNextToken();
		if (CurTok.type == SC)
		{
			getNextToken();
			return std::move(
				std::make_unique<RETURN_STMT>(true, nullptr, CurTok));
		}

		auto expr = ParseExpr();
		if (expr)
		{

			if (CurTok.type == SC)
			{
				getNextToken();
				return std::move(
					std::make_unique<RETURN_STMT>(
						false,
						std::move(expr),
						CurTok));
			}
			else
				return reportError("expected semicolon", CurTok);
		}
		else
			return nullptr;
	}
	else
		return reportError("Expected return", CurTok);
}

static std::unique_ptr<ASTnode> ParseWhile()
{
	if (CurTok.type == WHILE)
	{

		getNextToken();
		if (CurTok.type == LPAR)
		{
			getNextToken();
			auto expr = ParseExpr();
			if (expr)
			{

				if (CurTok.type == RPAR)
				{

					getNextToken();
					auto stmt = ParseStatement();
					if (stmt)
					{
						return std::move(
							std::make_unique<WHILE_STMT>(
								std::move(expr),
								std::move(stmt)));
					}
					else
						return nullptr;
				}
				else
					return reportError("Expected right paranthesis", CurTok);
			}
			else
				return nullptr;
		}
		else
			return reportError("Expected left paranthesis", CurTok);
	}
	else
		return reportError("Expected while token", CurTok);
}

static std::unique_ptr<ASTnode> ParseElseStmt()
{
	if (CurTok.type == ELSE)
	{
		getNextToken();
		auto block = ParseBlock();
		if (block)
		{

			return std::move(block);
		}
		else
			return nullptr;
	}
	else if (CurTok.type == MINUS || CurTok.type == NOT ||
			 CurTok.type == LPAR || CurTok.type == IDENT ||
			 CurTok.type == INT_LIT || CurTok.type == FLOAT_LIT ||
			 CurTok.type == BOOL_LIT || CurTok.type == RBRA ||
			 CurTok.type == LBRA || CurTok.type == WHILE ||
			 CurTok.type == IF || CurTok.type == RETURN)
	{
		return std::move(
			std::make_unique<Block>(nullptr, nullptr));
	}
	else
		return reportError("Expected else token", CurTok);
}

static std::unique_ptr<ASTnode> ParseIF()
{
	if (CurTok.type == IF)
	{
		getNextToken();
		if (CurTok.type == LPAR)
		{
			getNextToken();

			auto expr = ParseExpr();
			if (expr)
			{

				if (CurTok.type == RPAR)
				{

					getNextToken();
					auto trueBlock = ParseBlock();
					if (trueBlock)
					{
						auto falseBlock = ParseElseStmt();
						if (falseBlock)
						{

							return std::move(
								std::make_unique<IF_STMT>(
									std::move(expr),
									std::move(trueBlock),
									std::move(falseBlock)));
						}
						else
							return nullptr;
					}
					else
						return nullptr;
				}
				else
					return reportError("Expected right paranthesis", CurTok);
			}
			else
				return nullptr;
		}
		else
			return reportError("Expected left paranthesis", CurTok);
	}
	else
		return reportError("Expected if token", CurTok);
}

static std::unique_ptr<ASTnode> ParseExprSTMT()
{
	if (CurTok.type == MINUS || CurTok.type == NOT ||
		CurTok.type == IDENT || CurTok.type == INT_LIT ||
		CurTok.type == FLOAT_LIT || CurTok.type == BOOL_LIT ||
		CurTok.type == LPAR)
	{
		auto expr = ParseExpr();
		if (expr)
		{

			if (CurTok.type == SC)
			{
				getNextToken();
				return std::move(
					std::make_unique<EXPR_STMT>(
						std::move(expr), false));
			}
			else
				return reportError("Expected semicolon", CurTok);
		}
		else
			return nullptr;
	}
	if (CurTok.type == SC)
	{
		getNextToken();
		return std::move(
			std::make_unique<EXPR_STMT>(
				nullptr, true));
	}
	else
		return reportError("Expected semicolon", CurTok);
}

static std::unique_ptr<ASTnode> ParseStatement()
{
	if (CurTok.type == MINUS || CurTok.type == NOT ||
		CurTok.type == IDENT || CurTok.type == INT_LIT ||
		CurTok.type == FLOAT_LIT || CurTok.type == BOOL_LIT ||
		CurTok.type == LPAR || CurTok.type == SC)
	{
		auto exprStmt = ParseExprSTMT();
		if (exprStmt)
		{
			return std::move(
				std::make_unique<STMT>(
					std::move(exprStmt),
					nullptr,
					nullptr,
					nullptr,
					nullptr));
		}
		else
			return nullptr;
	}

	else if (CurTok.type == LBRA)
	{
		auto block = ParseBlock();
		if (block)
		{

			return std::move(
				std::make_unique<STMT>(
					nullptr,
					std::move(block),
					nullptr,
					nullptr,
					nullptr));
		}
		else
			return nullptr;
	}
	else if (CurTok.type == IF)
	{
		auto if_tok = ParseIF();
		if (if_tok)
		{

			return std::move(
				std::make_unique<STMT>(
					nullptr,
					nullptr,
					std::move(if_tok),
					nullptr,
					nullptr));
		}
		else
			return nullptr;
	}
	else if (CurTok.type == WHILE)
	{
		auto while_tok = ParseWhile();
		if (while_tok)
		{
			return std::move(
				std::make_unique<STMT>(
					nullptr,
					nullptr,
					nullptr,
					std::move(while_tok),
					nullptr));
		}
		else
			return nullptr;
	}
	else if (CurTok.type == RETURN)
	{
		auto return_tok = ParseReturn();
		if (return_tok)
		{
			return std::move(
				std::make_unique<STMT>(
					nullptr,
					nullptr,
					nullptr,
					nullptr,
					std::move(return_tok)));
		}
		else
			return nullptr;
	}
	return nullptr;
}

static std::unique_ptr<ASTnode> ParseStatementList()
{
	std::vector<std::unique_ptr<ASTnode>> stmtList;

	while (CurTok.type == MINUS || CurTok.type == NOT ||
		   CurTok.type == IDENT || CurTok.type == INT_LIT ||
		   CurTok.type == FLOAT_LIT || CurTok.type == BOOL_LIT ||
		   CurTok.type == LBRA || CurTok.type == IF ||
		   CurTok.type == WHILE || CurTok.type == RETURN ||
		   CurTok.type == LPAR || CurTok.type == SC)
	{
		auto stmt = ParseStatement();
		if (stmt)
		{
			stmtList.push_back(std::move(stmt));
		}
		else
			return nullptr;
	}

	return std::move(
		std::make_unique<STMTlist>(
			std::move(stmtList)));
}

static std::unique_ptr<ASTnode> ParseLocalDeclaration()
{
	std::string type;
	if (CurTok.type == INT_TOK)
	{
		type = "int";
	}
	else if (CurTok.type == FLOAT_TOK)
	{
		type = "float";
	}
	else if (CurTok.type == BOOL_TOK)
	{
		type = "bool";
	}
	else
		return reportError("Expected int, float or bool", CurTok);
	getNextToken();

	auto ID = ParseID();
	if (ID)
	{

		if (CurTok.type == SC)
		{

			getNextToken();
			return std::move(
				std::make_unique<LocalDeclaration>(type, std::move(ID)));
		}
		else
			return reportError("Expected semicolon", CurTok);
	}
	else
		return reportError("Expected identificator", CurTok);
}

static std::unique_ptr<ASTnode> ParseLocalDeclarations()
{
	std::vector<std::unique_ptr<ASTnode>> localDeclarations;

	while (CurTok.type == INT_TOK || CurTok.type == FLOAT_TOK || CurTok.type == BOOL_TOK)
	{
		auto localDeclaration = ParseLocalDeclaration();
		if (localDeclaration)
		{

			localDeclarations.push_back(std::move(localDeclaration));
		}
		else
			return nullptr;
	}

	return std::move(
		std::make_unique<LocalDeclarations>(
			std::move(localDeclarations)));
}

static std::unique_ptr<Param> ParseParam()
{
	std::string type;

	if (CurTok.type == INT_TOK)
	{
		type = "int";
	}
	if (CurTok.type == FLOAT_TOK)
	{
		type = "float";
	}
	if (CurTok.type == BOOL_TOK)
	{
		type = "bool";
	}
	getNextToken();

	auto id = ParseID();
	if (id)
	{
		return std::move(
			std::make_unique<Param>(type, std::move(id)));
	}

	return nullptr;
}

static std::unique_ptr<Params> ParseParams()
{
	std::vector<std::unique_ptr<Param>> params;
	while (CurTok.type == INT_TOK || CurTok.type == FLOAT_TOK || CurTok.type == BOOL_TOK)
	{
		auto param = ParseParam();
		if (param)
		{
			params.push_back(std::move(param));
		}
		else
			return nullptr;

		if (CurTok.type == COMMA)
			getNextToken();
		else
			break;
	}
	if (CurTok.type == VOID_TOK && params.size() == 0)
	{
		getNextToken();
		return std::move(
			std::make_unique<Params>(
				std::move(params),
				"void"));
	}
	else if (CurTok.type == VOID_TOK && params.size() != 0)
		return nullptr;

	if (CurTok.type == RPAR)
	{
		return std::move(
			std::make_unique<Params>(
				std::move(params),
				""));
	}
	else
		return nullptr;
}

static std::unique_ptr<ASTnode> ParseFunction(std::string type, std::unique_ptr<IDENTIFICATOR> ID)
{
	getNextToken();
	auto params = ParseParams();
	if (params)
	{
		if (CurTok.type == RPAR)
		{
			getNextToken();
			auto block = ParseBlock();
			if (block)
			{
				return std::move(
					std::make_unique<FunctionDeclaration>(
						type,
						std::move(ID),
						std::move(params),
						std::move(block)));
			}
			else
				return nullptr;
		}
		else
			return reportError("Expected right paranthesis", CurTok);
	}
	else
		return reportError("Expected parameters", CurTok);
}

static std::unique_ptr<ASTnode> functionDecisionBlock(bool isFunction, std::string type)
{
	getNextToken();
	auto id = ParseID();
	if (id)
	{
		if (CurTok.type == SC)
		{
			if (isFunction)
				return reportError("Void variable not allowed", CurTok);
			else
			{
				getNextToken();
				return std::move(
					std::make_unique<Declaration>(
						std::move(std::make_unique<VariableDeclaration>(type, std::move(id))),
						nullptr));
			}
		}
		else if (CurTok.type == LPAR)
		{
			auto function = ParseFunction(type, std::move(id));
			if (function)
			{
				return std::move(
					std::make_unique<Declaration>(
						nullptr,
						std::move(function)));
			}
			else
				return nullptr;
		}
		else if (isFunction)
			return reportError("Expected semicolon or left paranthesis", CurTok);
		else
			return reportError("Expected left paranthesis", CurTok);
	}
	else
		return nullptr;
}

static std::unique_ptr<ASTnode> ParseDeclaration()
{
	std::string type;
	if (CurTok.type == VOID_TOK)
	{
		type = "void";
		return functionDecisionBlock(true, "void");
	}
	else if (CurTok.type == INT_TOK)
	{
		type = "int";
	}
	else if (CurTok.type == FLOAT_TOK)
	{
		type = "float";
	}
	else if (CurTok.type == BOOL_TOK)
	{
		type = "bool";
	}
	else
		return reportError("Expected int, float, bool", CurTok);

	return functionDecisionBlock(false, type);
}

static std::unique_ptr<ASTnode> ParseExtern()
{
	if (CurTok.type == EXTERN)
	{

		getNextToken();
		std::string typeSpec = CurTok.lexeme;
		if (CurTok.type == VOID_TOK || CurTok.type == INT_TOK || CurTok.type == FLOAT_TOK || CurTok.type == BOOL_TOK)
		{
			getNextToken();
			auto id = ParseID();
			if (id)
			{

				if (CurTok.type == LPAR)
				{

					getNextToken();
					auto params = ParseParams();
					if (params)
					{
						if (CurTok.type == RPAR)
						{

							getNextToken();
							if (CurTok.type == SC)
							{
								getNextToken();
								return std::move(std::make_unique<Extern>(typeSpec, std::move(id), std::move(params)));
							}
							else
								return reportError("Expected semicolon on line", CurTok);
						}
						else
							return reportError("Expected right paranthesis on line", CurTok);
					}
					else
						return nullptr;
				}
				else
					return reportError("Expected left paranthesis on line", CurTok);
			}
			else
				return reportError("Expected variable definition on line", CurTok);
		}
		else
			return reportError("Expected the type of extern on line", CurTok);
	}
	else
		return reportError("Expected extern on line", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> ParseDeclList()
{
	std::vector<std::unique_ptr<ASTnode>> declList;

	while (CurTok.type == VOID_TOK || CurTok.type == INT_TOK || CurTok.type == FLOAT_TOK || CurTok.type == BOOL_TOK)
	{
		auto declaration = ParseDeclaration();
		if (declaration)
		{
			declList.push_back(std::move(declaration));
		}
		else
			return nullptr;
	}
	if (CurTok.type == EOF_TOK)
		return std::move(
			std::make_unique<DeclarationList>(
				std::move(declList)));
	else
		reportError("Expected end of file", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> ParseExternList()
{
	std::vector<std::unique_ptr<ASTnode>> externList;
	while (CurTok.type == EXTERN)
	{
		auto externNode = ParseExtern();
		if (externNode)
		{
			externList.push_back(std::move(externNode));
		}
		else
			return nullptr;
	}
	if (CurTok.type == VOID_TOK || CurTok.type == INT_TOK || CurTok.type == FLOAT_TOK || CurTok.type == BOOL_TOK)
	{
		return std::move(
			std::make_unique<ExternList>(
				std::move(externList)));
	}
	else
		return reportError("Expected void, int, float, bool or extern", CurTok);
}

static std::unique_ptr<ASTnode> ParseProgram()
{
	if (CurTok.type == EXTERN)
	{
		auto externList = ParseExternList();
		if (externList)
		{
			auto declList = ParseDeclList();
			if (declList)
			{
				return std::move(
					std::make_unique<Program>(
						std::move(externList),
						std::move(declList)));
			}
		}
	}
	else if (CurTok.type == VOID_TOK || CurTok.type == INT_TOK || CurTok.type == FLOAT_TOK || CurTok.type == BOOL_TOK)
	{
		auto declList = ParseDeclList();
		if (declList)
		{
			return std::move(
				std::make_unique<Program>(
					nullptr,
					std::move(declList)));
		}
	}
	else
		return reportError("Expected extern, void, int, float, bool on line", CurTok);

	return nullptr;
}

static std::unique_ptr<ASTnode> MainParserDriver()
{
	if (CurTok.type == EXTERN || CurTok.type == VOID_TOK || CurTok.type == INT_TOK || CurTok.type == FLOAT_TOK || CurTok.type == BOOL_TOK)
	{
		auto programTree = ParseProgram();
		if (programTree)
		{
			getNextToken();
			if (CurTok.type == EOF_TOK)
			{
				return std::move(programTree);
			}
			else
				return reportError("Expected end of file", CurTok);
		}
		else
			return nullptr;
	}
	else if (CurTok.type == EOF_TOK)
	{
		return std::move(nullptr);
	}
	else
		return reportError("Expected extern, void, int, float, bool on line", CurTok);
}

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const ASTnode &ast);

static void parser()
{
	// add body
	auto tree = MainParserDriver();
	if (tree == nullptr)
	{
		return;
	}
	// llvm::outs() << *tree << "\n";
	tree->codegen();
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;
static LinkedTable *VariableScopes;

//Function thta reports errors
Value *reportErrorLexer(std::string err)
{
	std::cout << "\033[31m" << "[Lexer Error] " << "\033[0m"; 
	std::cout << err << std::endl;
	return nullptr;
}

//Function that allocate memory for a variable. (taken from Kaleidoscope 7)
static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction, const std::string &name, Type *type)
{
	IRBuilder<> TmpB(&TheFunction->getEntryBlock(), TheFunction->getEntryBlock().begin());
	auto k = TmpB.CreateAlloca(type, 0, name.c_str());
	k->setAlignment(Align(4));
	return k;
}

//Function that creates different operations for float operands
static Value *generateCMP_float(int OP, Value *LHS, Value *RHS)
{
	switch (OP)
	{
	case PLUS:
		return Builder.CreateFAdd(LHS, RHS, "faddtmp");

	case MINUS:
		if (!RHS)
			return Builder.CreateFNeg(LHS, "fmintmp");
		else
			return Builder.CreateFSub(LHS, RHS, "fsubtmp");

	case ASTERIX:
		return Builder.CreateFMul(LHS, RHS, "fmultmp");

	case DIV:
		return Builder.CreateFDiv(LHS, RHS, "fdivtmp");

	case MOD:
		return Builder.CreateFRem(LHS, RHS, "fmodtmp");

	case NOT:
	case EQ:
		return Builder.CreateFCmpUEQ(LHS, RHS, "feqtmp");

	case NE:
		return Builder.CreateFCmpUNE(LHS, RHS, "fnetmp");

	case LE:
		return Builder.CreateFCmpULE(LHS, RHS, "fletmp");

	case LT:
		return Builder.CreateFCmpULT(LHS, RHS, "flttmp");

	case GE:
		return Builder.CreateFCmpUGE(LHS, RHS, "fgetmp");

	case GT:
		return Builder.CreateFCmpUGT(LHS, RHS, "fgttmp");

	default:
		return reportErrorLexer("Invalid binary operator");
	}
}

//Function that creates different operations for int operands
static Value *generateCMP_int(int OP, Value *LHS, Value *RHS)
{
	switch (OP)
	{
	case PLUS:
		return Builder.CreateAdd(LHS, RHS, "addtmp");

	case MINUS:
		if (!RHS)
			return Builder.CreateNeg(LHS, "mintmp");
		else
			return Builder.CreateSub(LHS, RHS, "subtmp");

	case ASTERIX:
		return Builder.CreateMul(LHS, RHS, "multmp");

	case DIV:
		return Builder.CreateSDiv(LHS, RHS, "divtmp");

	case MOD:
		return Builder.CreateSRem(LHS, RHS, "modtmp");

	case NOT:
	case EQ:
		return Builder.CreateICmpEQ(LHS, RHS, "eqtmp");

	case NE:
		return Builder.CreateICmpNE(LHS, RHS, "netmp");

	case LE:
		return Builder.CreateICmpSLE(LHS, RHS, "letmp");

	case LT:
		return Builder.CreateICmpSLT(LHS, RHS, "lttmp");

	case GE:
		return Builder.CreateICmpSGE(LHS, RHS, "getmp");

	case GT:
		return Builder.CreateICmpSGT(LHS, RHS, "gttmp");

	default:
		return reportErrorLexer("Invalid binary operator");
	}
}

//Function that handels the AND and OR lazy eval
static Value *createAND_OR_OP(int OP, Value *LHS, Value *RHS)
{
	std::string node_name = "";
	if (OP == AND)
	{
		node_name = "andtmp";
	}
	else if (OP == OR)
	{
		node_name = "ortmp";
	}

	Function *F = Builder.GetInsertBlock()->getParent();

	BasicBlock *lhs_eval = BasicBlock::Create(TheContext, "LHS_EVAL", F);
	BasicBlock *rhs_eval = BasicBlock::Create(TheContext, "RHS_EVAL");
	BasicBlock *continue_b = BasicBlock::Create(TheContext, "CONTINUE");

	Builder.CreateBr(lhs_eval);

	Builder.SetInsertPoint(lhs_eval);

	if (LHS->getType() == Type::getFloatTy(TheContext))
	{
		LHS = Builder.CreateFCmpUNE(LHS, ConstantFP::get(Type::getFloatTy(TheContext), 0.0), node_name);
	}
	else if (LHS->getType() == Type::getInt32Ty(TheContext))
	{
		LHS = Builder.CreateICmpNE(LHS, ConstantInt::get(Type::getInt32Ty(TheContext), 0), node_name);
	}
	else if (LHS->getType() == Type::getInt1Ty(TheContext))
	{
		LHS = Builder.CreateICmpNE(LHS, ConstantInt::get(Type::getInt1Ty(TheContext), 0), node_name);
	}

	if (OP == AND)
		Builder.CreateCondBr(LHS, rhs_eval, continue_b);
	else if (OP == OR)
		Builder.CreateCondBr(LHS, continue_b, rhs_eval);

	lhs_eval = Builder.GetInsertBlock();

	F->getBasicBlockList().push_back(rhs_eval);
	Builder.SetInsertPoint(rhs_eval);

	if (RHS->getType() == Type::getFloatTy(TheContext))
	{
		RHS = Builder.CreateFCmpUNE(RHS, ConstantFP::get(Type::getFloatTy(TheContext), 0.0), node_name);
	}
	else if (RHS->getType() == Type::getInt32Ty(TheContext))
	{
		RHS = Builder.CreateICmpNE(RHS, ConstantInt::get(Type::getInt32Ty(TheContext), 0.0), node_name);
	}
	else if (RHS->getType() == Type::getInt1Ty(TheContext))
	{
		RHS = Builder.CreateICmpNE(RHS, ConstantInt::get(Type::getInt1Ty(TheContext), 0.0), node_name);
	}

	Builder.CreateBr(continue_b);
	rhs_eval = Builder.GetInsertBlock();

	F->getBasicBlockList().push_back(continue_b);
	Builder.SetInsertPoint(continue_b);

	PHINode *PN = Builder.CreatePHI(Type::getInt1Ty(TheContext), 2, "andtmp");

	PN->addIncoming(LHS, lhs_eval);
	PN->addIncoming(RHS, rhs_eval);

	return PN;
}

Value *IntLit::codegen()
{
	return ConstantInt::get(Type::getInt32Ty(TheContext), Val);
}

Value *FloatLit::codegen()
{
	return ConstantFP::get(Type::getFloatTy(TheContext), Val);
}

Value *BoolLit::codegen()
{
	int k = 0;
	if (Val)
		k = 1;
	else if (!Val)
		k = 0;
	return ConstantInt::get(Type::getInt1Ty(TheContext), Val);
}

Value *FunctionArgs::codegen()
{
	return nullptr;
}

Value *FunctionCall::codegen()
{
	Function *CalleeF = TheModule->getFunction(ID->getVarName());
	if (!CalleeF)
		return reportErrorLexer("Unknown function called on line " + std::to_string(ID->getVarToken().lineNo) + ", column " + std::to_string(ID->getVarToken().columnNo));

	if (CalleeF->arg_size() != Args->ArgumentsArr.size())
		return reportErrorLexer("Incorrect number of arguments passed for function " + ID->getVarName() + ", on line " + std::to_string(ID->getVarToken().lineNo) + ", column " + std::to_string(ID->getVarToken().columnNo));

	std::vector<Value *> ArgsV;

	int i = 0;
	for (auto &Arg : CalleeF->args())
	{
		Value *v = Args->ArgumentsArr[i]->codegen();
		if (v->getType() != Arg.getType())
		{
			return reportErrorLexer(std::to_string(i + 1) + "th argument for function " + ID->getVarName() + " does not match the type, on line " + std::to_string(ID->getVarToken().lineNo) + ", column " + std::to_string(ID->getVarToken().columnNo));
		}
		ArgsV.push_back(v);
		i++;
	}

	return Builder.CreateCall(CalleeF, ArgsV, "calltmp");
}

Value *Element::codegen()
{
	if (Expression)
	{
		return Expression->codegen();
	}
	else if (ID)
	{
		if (VariableScopes->get(ID->getVarName()) == nullptr)
			return reportErrorLexer("Variable not defined on line " +
									std::to_string(ID->getVarToken().lineNo) +
									", column no" +
									std::to_string(ID->getVarToken().columnNo));

		auto load = Builder.CreateLoad(VariableScopes->get(ID->getVarName())->second, ID->getVarName());
		load->setAlignment(Align(4));
		return load;
	}
	else if (FunctionCall_s)
	{
		return FunctionCall_s->codegen();
	}
	else if (Literal)
	{
		return Literal->codegen();
	}
	return nullptr;
}

Value *UnaryOp::codegen()
{
	Value *expr = EXPR->codegen();
	if (expr->getType() == Type::getFloatTy(TheContext))
	{
		if (OP == NOT)
			return generateCMP_float(OP, expr, ConstantFP::get(Type::getFloatTy(TheContext), 0.0));
		else
			return generateCMP_float(OP, expr, nullptr);
	}
	else if (expr->getType() == Type::getInt32Ty(TheContext))
	{
		if (OP == NOT)
			return generateCMP_int(OP, expr, ConstantInt::get(Type::getInt32Ty(TheContext), 0));
		else
			return generateCMP_int(OP, expr, nullptr);
	}
	if (expr->getType() == Type::getInt1Ty(TheContext))
	{
		Builder.CreateZExt(expr, Type::getInt1Ty(TheContext), "expr_tmp_cnv_ui_si");
		if (OP == NOT)
			return generateCMP_int(OP, expr, ConstantInt::get(Type::getInt1Ty(TheContext), 0));
		else
			return generateCMP_int(OP, expr, nullptr);
	}
	return nullptr;
}

Value *BinOp::codegen()
{

	if (OP != AND && OP != OR)
	{
		auto *LHS = Left->codegen();
		auto *RHS = Right->codegen();

		Type *L = LHS->getType();
		Type *R = RHS->getType();

		if (L == Type::getFloatTy(TheContext) && R == Type::getFloatTy(TheContext))
		{
			return generateCMP_float(OP, LHS, RHS);
		}
		else if (L == Type::getFloatTy(TheContext) && R != Type::getFloatTy(TheContext))
		{
			if (R == Type::getInt1Ty(TheContext))
			{
				RHS = Builder.CreateUIToFP(RHS, Type::getFloatTy(TheContext), "rhs_tmp_cnv_ui_fp");
			}
			else
			{
				RHS = Builder.CreateSIToFP(RHS, Type::getFloatTy(TheContext), "rhs_tmp_cnv_si_fp");
			}
			return generateCMP_float(OP, LHS, RHS);
		}
		else if (L != Type::getFloatTy(TheContext) && R == Type::getFloatTy(TheContext))
		{
			if (L == Type::getInt1Ty(TheContext))
			{
				LHS = Builder.CreateUIToFP(LHS, Type::getFloatTy(TheContext), "lhs_tmp_cnv_ui_fp");
			}
			else
			{
				LHS = Builder.CreateSIToFP(LHS, Type::getFloatTy(TheContext), "lhs_tmp_cnv_si_fp");
			}
			return generateCMP_float(OP, LHS, RHS);
		}
		else
		{
			if (L == Type::getInt1Ty(TheContext))
			{
				LHS = Builder.CreateZExt(LHS, Type::getInt32Ty(TheContext), "lhs_tmp_cnv_ui_si");
			}
			if (R == Type::getInt1Ty(TheContext))
			{
				RHS = Builder.CreateZExt(RHS, Type::getInt32Ty(TheContext), "rhs_tmp_cnv_ui_si");
			}
			return generateCMP_int(OP, LHS, RHS);
		}
	}
	else if (OP == AND || OP == OR)
	{
		auto *LHS = Left->codegen();
		auto *RHS = Right->codegen();
		return createAND_OR_OP(OP, LHS, RHS);
	}

	return nullptr;
}

Value *IDENTIFICATOR::codegen()
{
	return nullptr;
}

Value *EXPR::codegen()
{
	if (!ID)
	{
		return BinOPERATOR->codegen();
	}
	else
	{
		if (VariableScopes->get(ID->getVarName()) == nullptr)
			return reportErrorLexer("Variable not defined on line " +
									std::to_string(ID->getVarToken().lineNo) +
									", column no " +
									std::to_string(ID->getVarToken().columnNo));

		auto exprVal = BinOPERATOR->codegen();
		if (!exprVal)
			return nullptr;

		Value *toBeStored = VariableScopes->get(ID->getVarName())->second;
		std::string toCheckType = VariableScopes->get(ID->getVarName())->first;

		Type *toBeStoredType;

		if (toCheckType == "float")
		{
			toBeStoredType = Type::getFloatTy(TheContext);
		}
		else if (toCheckType == "int")
		{
			toBeStoredType = Type::getInt32Ty(TheContext);
		}
		else if (toCheckType == "bool")
		{
			toBeStoredType = Type::getInt1Ty(TheContext);
		}

		if (exprVal->getType() != toBeStoredType)
		{
			if (toBeStoredType == Type::getFloatTy(TheContext))
			{
				if (exprVal->getType() == Type::getInt32Ty(TheContext))
				{
					exprVal = Builder.CreateSIToFP(exprVal, Type::getFloatTy(TheContext), "exprValAssgn_tmp_cnv_si_fp");
				}
				else if (exprVal->getType() == Type::getInt1Ty(TheContext))
				{
					exprVal = Builder.CreateUIToFP(exprVal, Type::getFloatTy(TheContext), "exprValAssgn_tmp_cnv_ui_fp");
				}
				else
					return reportErrorLexer("Could not assign value due to invalid implicit convertion");
			}
			if (toBeStoredType == Type::getInt32Ty(TheContext))
			{
				if (exprVal->getType() == Type::getFloatTy(TheContext))
				{
					exprVal = Builder.CreateFPToSI(exprVal, Type::getInt32Ty(TheContext), "exprValAssgn_tmp_cnv_fp_si");
				}
				else if (exprVal->getType() == Type::getInt1Ty(TheContext))
				{
					exprVal = Builder.CreateZExt(exprVal, Type::getInt32Ty(TheContext), "exprValAssgn_tmp_cnv_ui_si");
				}
				else
					return reportErrorLexer("Could not assign value due to invalid implicit convertion");
			}
			if (toBeStoredType == Type::getInt1Ty(TheContext))
			{
				if (exprVal->getType() == Type::getFloatTy(TheContext))
				{
					exprVal = Builder.CreateFPToUI(exprVal, Type::getInt1Ty(TheContext), "exprValAssgn_tmp_cnv_fp_ui");
				}
				else if (exprVal->getType() == Type::getInt32Ty(TheContext))
				{
					exprVal = Builder.CreateZExt(exprVal, Type::getInt1Ty(TheContext), "exprValAssgn_tmp_cnv_si_ui");
				}
				else
					return reportErrorLexer("Could not assign value due to invalid implicit convertion");
			}
		}
		return Builder.CreateStore(exprVal, toBeStored);
	}
}

Value *EXPR_STMT::codegen()
{
	if (!isSemicolonOnly)
	{
		return Expression->codegen();
	}

	return nullptr;
}

Value *RETURN_STMT::codegen()
{
	if (NoExpr)
	{
		return Builder.CreateRetVoid();
	}
	else
	{
		auto expr = Expression->codegen();

		if (!expr)
		{
			return nullptr;
		}
		else
		{

			Function *F = Builder.GetInsertBlock()->getParent();

			if (expr->getType() != F->getReturnType())
			{
				return reportErrorLexer("Return type different than declared in function on line " + std::to_string(Tok.lineNo));
			}

			return Builder.CreateRet(expr);
		}
	}
	return nullptr;
}

Value *WHILE_STMT::codegen()
{
	Function *F = Builder.GetInsertBlock()->getParent();

	BasicBlock *COND_BB = BasicBlock::Create(TheContext, "WHILE_COND", F);
	BasicBlock *WHILE_BB = BasicBlock::Create(TheContext, "WHILE_BLOCK");
	BasicBlock *CONTINUE_BB = BasicBlock::Create(TheContext, "END_WHILE_BLOCK");

	Builder.CreateBr(COND_BB);
	Builder.SetInsertPoint(COND_BB);

	Value *CondV = Expression->codegen();
	if (!CondV)
		return nullptr;

	if (CondV->getType() == Type::getInt32Ty(TheContext))
	{
		CondV = Builder.CreateICmpNE(CondV, ConstantInt::get(Type::getInt32Ty(TheContext), 0), "START_WHILE_CONDITION");
	}
	if (CondV->getType() == Type::getFloatTy(TheContext))
	{
		CondV = Builder.CreateFCmpUNE(CondV, ConstantFP::get(Type::getFloatTy(TheContext), 0.0), "START_WHILE_CONDITION");
	}
	if (CondV->getType() == Type::getInt1Ty(TheContext))
	{
		CondV = Builder.CreateICmpNE(CondV, ConstantInt::get(Type::getInt1Ty(TheContext), 0), "START_WHILE_CONDITION");
	}
	Builder.CreateCondBr(CondV, WHILE_BB, CONTINUE_BB);

	F->getBasicBlockList().push_back(WHILE_BB);
	Builder.SetInsertPoint(WHILE_BB);

	Value *WHILE_BLOCK_V = STMT_s->codegen();

	Builder.CreateBr(COND_BB);

	F->getBasicBlockList().push_back(CONTINUE_BB);
	Builder.SetInsertPoint(CONTINUE_BB);

	return nullptr;
}

Value *IF_STMT::codegen()
{
	Value *CondV = Expression->codegen();
	if (!CondV)
		return nullptr;

	if (CondV->getType() == Type::getInt32Ty(TheContext))
	{
		CondV = Builder.CreateICmpNE(CondV, ConstantInt::get(Type::getInt32Ty(TheContext), 0), "START_IF_CONDITION");
	}
	if (CondV->getType() == Type::getFloatTy(TheContext))
	{
		CondV = Builder.CreateFCmpUNE(CondV, ConstantFP::get(Type::getFloatTy(TheContext), 0.0), "START_IF_CONDITION");
	}
	if (CondV->getType() == Type::getInt1Ty(TheContext))
	{
		CondV = Builder.CreateICmpNE(CondV, ConstantInt::get(Type::getInt1Ty(TheContext), 0), "START_IF_CONDITION");
	}
	Function *F = Builder.GetInsertBlock()->getParent();

	BasicBlock *TRUE_BB = BasicBlock::Create(TheContext, "IF_TRUE_BLOCK", F);
	BasicBlock *FALSE_BB = BasicBlock::Create(TheContext, "IF_FALSE_BLOCK");
	BasicBlock *CONTINUE_BB = BasicBlock::Create(TheContext, "END_IF_BLOCK");

	Builder.CreateCondBr(CondV, TRUE_BB, FALSE_BB);

	Builder.SetInsertPoint(TRUE_BB);

	Block_TRUE_s->codegen();

	Builder.CreateBr(CONTINUE_BB);

	TRUE_BB = Builder.GetInsertBlock();

	F->getBasicBlockList().push_back(FALSE_BB);
	Builder.SetInsertPoint(FALSE_BB);

	Block_FALSE->codegen();

	Builder.CreateBr(CONTINUE_BB);

	F->getBasicBlockList().push_back(CONTINUE_BB);
	Builder.SetInsertPoint(CONTINUE_BB);

	return nullptr;
}

Value *STMT::codegen()
{

	if (EXPR_s)
	{
		return EXPR_s->codegen();
	}
	if (Block_s)
	{
		return Block_s->codegen();
	}
	if (IF_s)
	{
		return IF_s->codegen();
	}
	if (WHILE_s)
	{
		return WHILE_s->codegen();
	}
	if (RETURN_s)
	{
		return RETURN_s->codegen();
	}
	return nullptr;
}

Value *STMTlist::codegen()
{

	for (int i = 0; i < STMT.size(); i++)
	{
		STMT[i]->codegen();
	}

	return nullptr;
}

Value *LocalDeclaration::codegen()
{
	if (VariableScopes->table[ID->getVarName()] != nullptr)
		return reportErrorLexer("Variable already defined on line " +
								std::to_string(ID->getVarToken().lineNo) +
								", column no " +
								std::to_string(ID->getVarToken().columnNo));

	Type *type;
	Function *F = Builder.GetInsertBlock()->getParent();
	AllocaInst *Alloca;

	if (VarType == "int")
	{
		type = Type::getInt32Ty(TheContext);
	}
	else if (VarType == "float")
	{
		type = Type::getFloatTy(TheContext);
	}
	else if (VarType == "bool")
	{
		type = Type::getInt1Ty(TheContext);
	}

	Alloca = CreateEntryBlockAlloca(F, ID->getVarName(), type);
	VariableScopes->put(ID->getVarName(), VarType, Alloca);

	return nullptr;
}

Value *LocalDeclarations::codegen()
{

	for (int i = 0; i < LocalDeclaration.size(); i++)
	{
		LocalDeclaration[i]->codegen();
	}

	return nullptr;
}

Value *Block::codegen()
{

	LinkedTable *oldScope = VariableScopes;
	VariableScopes = new LinkedTable(oldScope);

	if (LocalDeclarations)
	{
		LocalDeclarations->codegen();
	}

	if (STMTlist)
	{
		STMTlist->codegen();
	}

	VariableScopes = oldScope;

	return nullptr;
}

Value *FunctionDeclaration::codegen()
{
	std::vector<Type *> Parameters;

	if (_Params->VoidTok == "")
	{
		for (int i = 0; i < _Params->_ParameterList_.size(); i++)
		{
			std::string _type = _Params->_ParameterList_[i]->VarType;

			if (_type == "float")
			{
				Parameters.push_back(Type::getFloatTy(TheContext));
			}
			else if (_type == "bool")
			{
				Parameters.push_back(Type::getInt1Ty(TheContext));
			}
			else if (_type == "int")
			{
				Parameters.push_back(Type::getInt32Ty(TheContext));
			}
			
		}
	}

	FunctionType *FT;

	if (TypeSpec == "float")
	{
		FT = FunctionType::get(Type::getFloatTy(TheContext), Parameters, false);
	}
	else if (TypeSpec == "bool")
	{
		FT = FunctionType::get(Type::getInt1Ty(TheContext), Parameters, false);
	}
	else if (TypeSpec == "int")
	{
		FT = FunctionType::get(Type::getInt32Ty(TheContext), Parameters, false);
	}
	else if (TypeSpec == "void")
	{
		FT = FunctionType::get(Type::getVoidTy(TheContext), Parameters, false);
	}

	Function *F =
		Function::Create(FT, Function::ExternalLinkage, ID->getVarName(), TheModule.get());

	if (!F)
		return nullptr;

	BasicBlock *BB = BasicBlock::Create(TheContext, "entry", F);
	Builder.SetInsertPoint(BB);

	unsigned Idx = 0;
	AllocaInst *Alloca;
	LinkedTable *oldScope = VariableScopes;
	VariableScopes = new LinkedTable(oldScope);


	for (auto &Arg : F->args())
	{
		Arg.setName(_Params->getParam(Idx)->getName());
		Alloca = CreateEntryBlockAlloca(F, Arg.getName().str(), Arg.getType());
		Builder.CreateStore(&Arg, Alloca);

		std::string _Argtype = "";
		if (Arg.getType() == Type::getFloatTy(TheContext))
		{
			_Argtype = "float";
		}
		else if (Arg.getType() == Type::getInt1Ty(TheContext))
		{
			_Argtype = "bool";
		}
		else if (Arg.getType() == Type::getInt32Ty(TheContext))
		{
			_Argtype = "int";
		}

		VariableScopes->put(Arg.getName().str(), _Argtype, Alloca);
		Idx++;
	}

	Block->codegen();

	VariableScopes = oldScope;

	return F;
}

Value *VariableDeclaration::codegen()
{
	if (VariableScopes->table[ID->getVarName()] != nullptr)
		return reportErrorLexer("Variable already defined on line " +
								std::to_string(ID->getVarToken().lineNo) +
								", column no" +
								std::to_string(ID->getVarToken().columnNo));

	Type *type;

	if (VarType == "int")
	{
		type = Type::getInt32Ty(TheContext);
		auto constant = ConstantInt::get(Type::getInt32Ty(TheContext), 0);

		auto var = new GlobalVariable(*TheModule, type, false, GlobalVariable::CommonLinkage, constant, ID->getVarName());
		var->setAlignment(Align(4));

		VariableScopes->put(ID->getVarName(), VarType, var);

		return var;
	}
	else if (VarType == "float")
	{
		type = Type::getFloatTy(TheContext);
		auto constant = ConstantFP::get(Type::getFloatTy(TheContext), 0.0f);

		auto var = new GlobalVariable(*TheModule, type, false, GlobalVariable::CommonLinkage, constant, ID->getVarName());
		var->setAlignment(Align(4));

		VariableScopes->put(ID->getVarName(), VarType, var);

		return var;
	}
	else if (VarType == "bool")
	{
		type = Type::getInt1Ty(TheContext);
		auto constant = ConstantInt::get(Type::getInt1Ty(TheContext), 0);

		auto var = new GlobalVariable(*TheModule, type, false, GlobalVariable::CommonLinkage, constant, ID->getVarName());
		var->setAlignment(Align(4));

		VariableScopes->put(ID->getVarName(), VarType, var);

		return var;
	}

	return nullptr;
}

Value *Declaration::codegen()
{
	if (VariableDeclaration)
	{
		Value *varDeclaration = VariableDeclaration->codegen();
	}

	if (FunctionDeclaration)
	{
		Value *funcDeclaration = FunctionDeclaration->codegen();
	}
	return nullptr;
}

Value *DeclarationList::codegen()
{

	for (int i = 0; i < Declarations.size(); i++)
	{
		Declarations[i]->codegen();
	}

	return nullptr;
}

Value *Extern::codegen()
{
	std::vector<Type *> Parameters;

	if (_Params->VoidTok == "")
	{
		for (int i = 0; i < _Params->_ParameterList_.size(); i++)
		{
			std::string _type = _Params->_ParameterList_[i]->VarType;

			if (_type == "float")
			{
				Parameters.push_back(Type::getFloatTy(TheContext));
			}
			else if (_type == "bool")
			{
				Parameters.push_back(Type::getInt1Ty(TheContext));
			}
			else if (_type == "int")
			{
				Parameters.push_back(Type::getInt32Ty(TheContext));
			}
		}
	}

	FunctionType *FT;

	if (TypeSpec == "float")
	{
		FT = FunctionType::get(Type::getFloatTy(TheContext), Parameters, false);
	}
	else if (TypeSpec == "bool")
	{
		FT = FunctionType::get(Type::getInt1Ty(TheContext), Parameters, false);
	}
	else if (TypeSpec == "int")
	{
		FT = FunctionType::get(Type::getInt32Ty(TheContext), Parameters, false);
	}
	else if (TypeSpec == "void")
	{
		FT = FunctionType::get(Type::getVoidTy(TheContext), Parameters, false);
	}

	Function *F =
		Function::Create(FT, Function::ExternalLinkage, ID->getVarName(), TheModule.get());

	unsigned Idx = 0;
	for (auto &Arg : F->args())
		Arg.setName(_Params->getParam(Idx++)->getName());

	if (!F)
		return nullptr;

	return nullptr;
}

Value *ExternList::codegen()
{
	for (int i = 0; i < Externs.size(); i++)
	{
		Externs[i]->codegen();
	}

	return nullptr;
}

Value *Program::codegen()
{
	VariableScopes = new LinkedTable(nullptr);
	if (ExternList)
	{
		Value *externListParse = ExternList->codegen();
	}

	if (DeclarationList)
	{
		Value *declarationListParse = DeclarationList->codegen();
	}

	return nullptr;
}

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const ASTnode &ast)
{
	os << ast.to_string();
	return os;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main(int argc, char **argv)
{
	if (argc == 2)
	{
		pFile = fopen(argv[1], "r");
		if (pFile == NULL)
			perror("Error opening file");
	}
	else
	{
		std::cout << "Usage: ./code InputFile\n";
		return 1;
	}

	// initialize line number and column numbers to zero
	lineNo = 1;
	columnNo = 1;

	// get the first token
	getNextToken();
	// while (CurTok.type != EOF_TOK)
	// {
	// 	fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
	// 			CurTok.type);
	// 	getNextToken();
	// }
	// fprintf(stderr, "Lexer Finished\n");

	// Make the module, which holds all the code.
	TheModule = std::make_unique<Module>("mini-c", TheContext);

	// Run the parser now.
	parser();
	fprintf(stderr, "Parsing Finished\n");

	//********************* Start printing final IR **************************
	// Print out all of the generated code into a file called output.ll
	auto Filename = "output.ll";
	std::error_code EC;
	raw_fd_ostream dest(Filename, EC, sys::fs::F_None);

	if (EC)
	{
		errs() << "Could not open file: " << EC.message();
		return 1;
	}
	// TheModule->print(errs(), nullptr); // print IR to terminal
	TheModule->print(dest, nullptr);
	//********************* End printing final IR ****************************

	fclose(pFile); // close the file that contains the code that was parsed
	return 0;
}