package hu.bme.mit.inf.ttmc.code.simplifier.visitor;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst.Operator;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.simplifier.SimplifyAstVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.StatementListAst;

public class AssignmentUnrollVisitor extends SimplifyAstVisitor {

	@Override
	public StatementAst visit(ExpressionStatementAst ast) {
		ExpressionAst expr = ast.getExpression();
		
		if (expr instanceof BinaryExpressionAst) {
			return this.unrollBinaryExpressionStatement(ast, (BinaryExpressionAst) expr);
		}
		
		return super.visit(ast);
	}

	private StatementAst unrollBinaryExpressionStatement(ExpressionStatementAst ast, BinaryExpressionAst expr) {
		// Unroll assignments
		if (expr.getOperator() == Operator.OP_ASSIGN) {
			Deque<BinaryExpressionAst> binaryExpressions = new ArrayDeque<>();
			// Find the rightmost element
			binaryExpressions.add(expr);
			ExpressionAst rhs = expr.getRight();
			while (rhs instanceof BinaryExpressionAst && ((BinaryExpressionAst) rhs).getOperator() == Operator.OP_ASSIGN) {
				BinaryExpressionAst binary = (BinaryExpressionAst) rhs;
				rhs = binary.getRight();
				binaryExpressions.add(binary);
			}
			
			List<StatementAst> stmts = new ArrayList<>();

			// Now go backwards
			while (!binaryExpressions.isEmpty()) {
				BinaryExpressionAst binExpr = binaryExpressions.removeLast();
				ExpressionAst lhs = binExpr.getLeft();
				
				stmts.add(new ExpressionStatementAst(new BinaryExpressionAst(lhs, rhs, Operator.OP_ASSIGN)));
				rhs = lhs;
			}
			
			return new StatementListAst(stmts);			
		}
		
		return ast;
	}

}
