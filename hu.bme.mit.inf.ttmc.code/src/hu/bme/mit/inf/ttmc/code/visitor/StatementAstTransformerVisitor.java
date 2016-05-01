package hu.bme.mit.inf.ttmc.code.visitor;

import java.util.ArrayList;
import java.util.List;
import hu.bme.mit.inf.ttmc.code.ast.AstNode;
import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CaseStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DefaultStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.GotoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.SwitchStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public abstract class StatementAstTransformerVisitor implements StatementVisitor<StatementAst> {

	public static class StatementListAst extends StatementAst {
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
	public StatementAst visit(IfStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(CompoundStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(DeclarationStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(ReturnStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(ExpressionStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(WhileStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(ForStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(DoStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(SwitchStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(CaseStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(DefaultStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(ContinueStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(BreakStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(GotoStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(LabeledStatementAst ast) {
		return ast;
	}

	public StatementAst visit(NullStatementAst ast) {
		return ast;
	}
	
}
