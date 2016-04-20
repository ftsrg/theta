package hu.bme.mit.inf.ttmc.code.visitor;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.code.ast.AstNode;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst.Operator;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.CloneAstVisitor;
import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class StatementUnrollAstVisitor extends CloneAstVisitor {

	private static class StatementListAst extends StatementAst {
		private List<StatementAst> stmts = new ArrayList<>();

		public StatementListAst(List<StatementAst> stmts) {
			this.stmts = stmts;
		}
		
		public List<StatementAst> getStatements() {
			return this.stmts;
		}
		
		@Override
		public <S> S accept(StatementVisitor<S> visitor) {
			throw new UnsupportedOperationException();
		}

		@Override
		public StatementAst copy() {
			throw new UnsupportedOperationException();
		}

		@Override
		public AstNode[] getChildren() {
			throw new UnsupportedOperationException();
		}		
	}
	

	@Override
	public StatementAst visit(CompoundStatementAst ast) {
		List<StatementAst> stmts = new ArrayList<>();
		for (StatementAst stmt : ast.getStatements()) {
			StatementAst res = stmt.accept(this);
			
			if (res instanceof StatementListAst) {
				stmts.addAll(((StatementListAst) res).getStatements());
			} else {
				stmts.add(res);
			}
		}
		
		return new CompoundStatementAst(stmts);
	}
	
	@Override
	public StatementAst visit(DeclarationStatementAst ast) {
		DeclarationAst decl = ast.getDeclaration();
		
		if (decl instanceof VarDeclarationAst) {
			List<DeclaratorAst> declarators = ((VarDeclarationAst) decl).getDeclarators();
			
			if (declarators.size() == 1)
				return ast;
			
			List<StatementAst> stmts = new ArrayList<>();
			for (DeclaratorAst declarator : declarators) {
				stmts.add(new DeclarationStatementAst(new VarDeclarationAst(((VarDeclarationAst) decl).getSpecifier(), ImmutableList.of(declarator))));
			}
			
			return new StatementListAst(stmts);
		}
		
		return ast;
	}
	
	@Override
	public StatementAst visit(ExpressionStatementAst ast) {
		ExpressionAst expr = ast.getExpression();
		
		if (expr instanceof BinaryExpressionAst) {
			return this.unrollBinaryExpressionStatement(ast, (BinaryExpressionAst) expr);
		}
		
		return new ExpressionStatementAst(expr);
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
