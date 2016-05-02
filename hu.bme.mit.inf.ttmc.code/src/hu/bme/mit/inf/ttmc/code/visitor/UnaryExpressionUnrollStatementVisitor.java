package hu.bme.mit.inf.ttmc.code.visitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.code.ast.AssignmentInitializerAst;
import hu.bme.mit.inf.ttmc.code.ast.AstNode;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationSpecifierAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionListAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst.Operator;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.DeclarationVisitor;
import hu.bme.mit.inf.ttmc.code.ast.visitor.ExpressionVisitor;

public class UnaryExpressionUnrollStatementVisitor extends StatementAstTransformerVisitor implements ExpressionVisitor<ExpressionAst> {
	
	private class LvalData {
		public String name;
		public String tempName;
		public BinaryExpressionAst.Operator op;
		
		public LvalData(String name, String tempName, BinaryExpressionAst.Operator op) {
			this.name = name;
			this.tempName = tempName;
			this.op = op;
		}
	}
	
	private List<NameExpressionAst> currLvals = new ArrayList<>();
	private Stack< List<LvalData> > lvalStack = new Stack<>();
	
	@Override
	public StatementAst visit(IfStatementAst ast) {
		ExpressionAst expr = ast.getCondition();

		this.lvalStack.add(new ArrayList<LvalData>());
		expr = expr.accept(this);
		
		List<StatementAst> stmts = new ArrayList<>();
		for (LvalData lval : this.lvalStack.lastElement()) {
			stmts.add(new DeclarationStatementAst(new VarDeclarationAst(
				new DeclarationSpecifierAst(), 
				new ArrayList<DeclaratorAst>() {{ add(new InitDeclaratorAst(lval.tempName, new AssignmentInitializerAst(new NameExpressionAst(lval.name)))); }}
			)));
			stmts.add(new ExpressionStatementAst(new BinaryExpressionAst(
				new NameExpressionAst(lval.name),
				new BinaryExpressionAst(
					new NameExpressionAst(lval.name),
					new LiteralExpressionAst(1),
					lval.op
				), BinaryExpressionAst.Operator.OP_ASSIGN
			)));
		}
		stmts.add(new IfStatementAst(expr, ast.getThen(), ast.getElse()));
		
		this.lvalStack.pop();
		
		return new StatementListAst(stmts);
	}
	
	@Override
	public StatementAst visit(WhileStatementAst ast) {
		ExpressionAst expr = ast.getCondition();
		
		return ast;
	}
	
	@Override
	public StatementAst visit(ExpressionStatementAst ast) {
		ExpressionAst expr = ast.getExpression();

		this.lvalStack.add(new ArrayList<LvalData>());
		expr = expr.accept(this);
		
		List<StatementAst> stmts = new ArrayList<>();
		for (LvalData lval : this.lvalStack.lastElement()) {
			stmts.add(new DeclarationStatementAst(new VarDeclarationAst(
				new DeclarationSpecifierAst(), 
				new ArrayList<DeclaratorAst>() {{ add(new InitDeclaratorAst(lval.tempName, new AssignmentInitializerAst(new NameExpressionAst(lval.name)))); }}
			)));
			stmts.add(new ExpressionStatementAst(new BinaryExpressionAst(
				new NameExpressionAst(lval.name),
				new BinaryExpressionAst(
					new NameExpressionAst(lval.name),
					new LiteralExpressionAst(1),
					lval.op
				), BinaryExpressionAst.Operator.OP_ASSIGN
			)));
		}
		stmts.add(new ExpressionStatementAst(expr));
		
		this.lvalStack.pop();
		
		return new StatementListAst(stmts);
	}

	
	private List<StatementAst> transformStatement(ExpressionAst expr) {
		expr = expr.accept(this);
		
		List<StatementAst> stmts = new ArrayList<>();
		for (LvalData lval : this.lvalStack.lastElement()) {
			stmts.add(new DeclarationStatementAst(new VarDeclarationAst(
				new DeclarationSpecifierAst(), 
				new ArrayList<DeclaratorAst>() {{ add(new InitDeclaratorAst(lval.tempName, new AssignmentInitializerAst(new NameExpressionAst(lval.name)))); }}
			)));
			stmts.add(new ExpressionStatementAst(new BinaryExpressionAst(
				new NameExpressionAst(lval.name),
				new BinaryExpressionAst(
					new NameExpressionAst(lval.name),
					new LiteralExpressionAst(1),
					lval.op
				), BinaryExpressionAst.Operator.OP_ASSIGN
			)));
		}
		
		return stmts;
	}

	@Override
	public ExpressionAst visit(BinaryExpressionAst ast) {
		return new BinaryExpressionAst(ast.getLeft().accept(this), ast.getRight().accept(this), ast.getOperator());
	}

	@Override
	public ExpressionAst visit(LiteralExpressionAst ast) {
		return ast;
	}

	@Override
	public ExpressionAst visit(NameExpressionAst ast) {
		return ast;
	}

	@Override
	public ExpressionAst visit(FunctionCallExpressionAst ast) {
		List<ExpressionAst> args = new ArrayList<>();
		for (ExpressionAst param : ast.getParams()) {
			args.add(param.accept(this));
		}		
		
		return new FunctionCallExpressionAst(ast.getName(), args);
	}

	@Override
	public ExpressionAst visit(UnaryExpressionAst ast) {
		UnaryExpressionAst.Operator operator = ast.getOperator();
		ExpressionAst operand = ast.getOperand().accept(this);
		
		if (operator == Operator.OP_PREFIX_INCR || operator == Operator.OP_PREFIX_DECR) {
			return new BinaryExpressionAst(operand, new BinaryExpressionAst(operand, new LiteralExpressionAst(1),
				operator == Operator.OP_PREFIX_INCR ? BinaryExpressionAst.Operator.OP_ADD : BinaryExpressionAst.Operator.OP_SUB
			), BinaryExpressionAst.Operator.OP_ASSIGN);
		}
		
		if (operator == Operator.OP_POSTFIX_INCR || operator == Operator.OP_POSTFIX_DECR) {
			//TODO Type check
			NameExpressionAst lval = (NameExpressionAst) operand;
			// Remember this expression
			LvalData data = new LvalData(
				lval.getName(),
				String.format("_tmpvar_%s", lval.getName()),
				operator == Operator.OP_POSTFIX_INCR ? BinaryExpressionAst.Operator.OP_ADD : BinaryExpressionAst.Operator.OP_SUB
			);
			this.lvalStack.lastElement().add(data);
			// Replace with a simple value
			return new NameExpressionAst(data.tempName);
		}
		
		return new UnaryExpressionAst(operand, operator);		
	}

	@Override
	public ExpressionAst visit(ExpressionListAst ast) {
		return ast;
	}
	
	
}
