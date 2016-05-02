package hu.bme.mit.inf.ttmc.code.visitor;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.AssignmentInitializerAst;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CaseStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.DefaultStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionListAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.ast.GotoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.SwitchStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.AstVisitor;

public class PrintCodeAstVisitor implements AstVisitor<String, String, String, String, String> {

	private int indent = 0;
	
	@Override
	public String visit(BinaryExpressionAst ast) {
		String left = ast.getLeft().accept(this);
		String right = ast.getRight().accept(this);
		
		return String.format("%s %s %s", left, binaryOperatorString(ast.getOperator()), right);
	}

	@Override
	public String visit(LiteralExpressionAst ast) {
		return String.format("%d", ast.getValue());
	}

	@Override
	public String visit(NameExpressionAst ast) {
		return String.format("%s", ast.getName());
	}

	@Override
	public String visit(FunctionCallExpressionAst ast) {
		StringBuilder sb = new StringBuilder();
		for (ExpressionAst arg : ast.getParams()) {
			sb.append(arg.accept(this));
		}
		
		return String.format("%s(%s)", ast.getName(), sb.toString());
	}

	@Override
	public String visit(UnaryExpressionAst ast) {
		switch (ast.getOperator()) {
		case OP_PREFIX_DECR:
		case OP_PREFIX_INCR:
		case OP_ASTERISK:
		case OP_MINUS:
		case OP_PLUS:
			return String.format("%s(%s)", ast.getOperator().toString(), ast.getOperand().accept(this));
		default:
			return String.format("(%s)%s", ast.getOperator().toString(), ast.getOperand().accept(this));
		}
	}

	@Override
	public String visit(ExpressionListAst ast) {
		List<String> members = new ArrayList<>();
		for (ExpressionAst expr : ast.getExpressions()) {
			members.add(expr.accept(this));
		}
		
		return String.join(",", members);
	}

	@Override
	public String visit(IfStatementAst ast) {
		StringBuilder sb = new StringBuilder();
		sb.append(String.format("if(%s) ", ast.getCondition().accept(this)));
		sb.append(ast.getThen().accept(this));
		
		if (ast.getElse() != null) {
			sb.append("else \n");
			sb.append(ast.getElse().accept(this));
		}
				
		return sb.toString();
	}

	@Override
	public String visit(CompoundStatementAst ast) {
		StringBuilder sb = new StringBuilder();
		
		this.indent++;
		String indentStr = new String(new char[this.indent*4]).replace('\0', ' ');
		
		sb.append("{\n");
		for (StatementAst stmt : ast.getStatements()) {
			sb.append(String.format("%s%s\n", indentStr, stmt.accept(this)));
		}
		this.indent--;
		sb.append(new String(new char[this.indent*4]).replace('\0', ' ') + '}');
		
		
		return sb.toString();
	}

	@Override
	public String visit(DeclarationStatementAst ast) {
		return String.format("%s;", ast.getDeclaration().accept(this));
	}

	@Override
	public String visit(ReturnStatementAst ast) {
		return String.format("return %s;", ast.getExpression().accept(this));
	}

	@Override
	public String visit(ExpressionStatementAst ast) {
		return String.format("%s;", ast.getExpression().accept(this));
	}

	@Override
	public String visit(WhileStatementAst ast) {
		return String.format("while (%s) %s", ast.getCondition().accept(this), ast.getBody().accept(this)); 
	}

	@Override
	public String visit(ForStatementAst ast) {
		return String.format("for (%s;%s;%s) %s", ast.getInit().accept(this), ast.getCondition().accept(this), ast.getIteration().accept(this), ast.getBody().accept(this));
	}

	@Override
	public String visit(DoStatementAst ast) {
		return String.format("do %s while (%s)\n", ast.getBody().accept(this), ast.getCondition().accept(this));
	}

	@Override
	public String visit(VarDeclarationAst ast) {
		List<String> declarators = new ArrayList<>();
		
		for (DeclaratorAst decl : ast.getDeclarators()) {
			declarators.add(decl.accept(this));
		}
		
		return String.format("int %s", String.join(", ", declarators));
	}

	@Override
	public String visit(FunctionDefinitionAst ast) {
		return String.format("%s\n%s", ast.getDeclarator().accept(this), ast.getBody().accept(this));
	}

	@Override
	public String visit(InitDeclaratorAst ast) {
		if (ast.getInitializer() instanceof AssignmentInitializerAst) {
			AssignmentInitializerAst init = (AssignmentInitializerAst) ast.getInitializer();
			return String.format("%s = %s", ast.getName(), init.getExpression().accept(this));
		}
		
		return ast.getName();
	}

	@Override
	public String visit(FunctionDeclaratorAst ast) {
		return String.format("%s()", ast.getName());
	}

	@Override
	public String visit(SwitchStatementAst ast) {
		return String.format("switch (%s)\n %s", ast.getExpression().accept(this), ast.getBody().accept(this));
	}

	@Override
	public String visit(CaseStatementAst ast) {
		return String.format("case %s:", ast.getExpression().accept(this));
	}

	@Override
	public String visit(DefaultStatementAst ast) {
		return "default;";
	}

	@Override
	public String visit(ContinueStatementAst ast) {
		return "continue;";
	}

	@Override
	public String visit(BreakStatementAst ast) {
		return "break;";
	}

	@Override
	public String visit(GotoStatementAst ast) {
		return String.format("goto %s;", ast.getLabel());
	}

	@Override
	public String visit(LabeledStatementAst ast) {
		return String.format("%s: %s", ast.getLabel(), ast.getStatement().accept(this));
	}

	@Override
	public String visit(NullStatementAst ast) {
		return ";";
	}

	@Override
	public String visit(TranslationUnitAst ast) {
		StringBuilder sb = new StringBuilder();
		
		for (DeclarationAst decl : ast.getDeclarations()) {
			sb.append(String.format("%s\n", decl.accept(this)));
		}
		
		return sb.toString();
	}

	private String binaryOperatorString(BinaryExpressionAst.Operator op) {
		switch (op) {
		case OP_ADD:
			return "+";
		case OP_ASSIGN:
			return "=";
		case OP_DIV:
			return "/";
		case OP_IS_EQ:
			return "==";
		case OP_IS_GT:
			return ">";
		case OP_IS_GTEQ:
			return ">=";
		case OP_IS_LT:
			return "<";
		case OP_IS_LTEQ:
			return "<=";
		case OP_IS_NOT_EQ:
			return "!=";
		case OP_MUL:
			return "*";
		case OP_SUB:
			return "-";			
		}
		throw new UnsupportedOperationException();
	}
	
	
}
