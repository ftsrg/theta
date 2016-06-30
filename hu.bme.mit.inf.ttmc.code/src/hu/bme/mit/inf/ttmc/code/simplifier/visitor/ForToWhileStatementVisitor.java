package hu.bme.mit.inf.ttmc.code.simplifier.visitor;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.simplifier.SimplifyAstVisitor;
import hu.bme.mit.inf.ttmc.code.simplifier.ast.TransformedWhileStatementAst;

public class ForToWhileStatementVisitor extends SimplifyAstVisitor {

	private int uniqid = 0;
	
	@Override
	public StatementAst visit(ForStatementAst ast) {
		// Resolve for statements into whiles
		StatementAst  init = ast.getInit().accept(this);
		ExpressionAst cond = ast.getCondition().accept(this);
		ExpressionAst iter = ast.getIteration().accept(this);
		StatementAst  body = ast.getBody().accept(this);
		
		StatementAst newBody;
		
		if (body instanceof CompoundStatementAst) {
			((CompoundStatementAst) body).getStatements().add(
				//new LabeledStatementAst(String.format("FOR_%d_ITER", ++uniqid), new ExpressionStatementAst(iter))
				new ExpressionStatementAst(iter)
			); // reference?
			newBody = body;
		} else {
			List<StatementAst> whileBody = new ArrayList<>();
			whileBody.add(body);
			whileBody.add(new LabeledStatementAst(String.format("FOR_%d_ITER", ++uniqid), new ExpressionStatementAst(iter)));
			newBody = new CompoundStatementAst(whileBody);
		}

		List<StatementAst> stmts = new ArrayList<>();
		stmts.add(init);
		stmts.add(new TransformedWhileStatementAst(cond, newBody));
		
		return new CompoundStatementAst(stmts);
	}
	
}
