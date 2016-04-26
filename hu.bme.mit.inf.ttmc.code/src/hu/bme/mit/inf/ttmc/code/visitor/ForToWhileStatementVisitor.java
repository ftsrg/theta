package hu.bme.mit.inf.ttmc.code.visitor;

import java.util.ArrayList;
import java.util.List;

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
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.SwitchStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

public class ForToWhileStatementVisitor implements StatementVisitor<StatementAst> {

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
		// Resolve for statements into whiles
		StatementAst  init = ast.getInit();
		ExpressionAst cond = ast.getCondition();
		ExpressionAst iter = ast.getIteration();
		StatementAst body  = ast.getBody();
		
		StatementAst newBody;
		
		if (body instanceof CompoundStatementAst) {
			((CompoundStatementAst) body).getStatements().add(new ExpressionStatementAst(iter));
			newBody = body;
		} else {
			List<StatementAst> whileBody = new ArrayList<>();
			whileBody.add(body);
			whileBody.add(new ExpressionStatementAst(iter));
			newBody = new CompoundStatementAst(whileBody);
		}
				
		List<StatementAst> stmts = new ArrayList<>();
		stmts.add(init);
		stmts.add(new WhileStatementAst(cond, newBody));
		
		return new CompoundStatementAst(stmts);
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

}
