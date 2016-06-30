package hu.bme.mit.inf.ttmc.code.simplifier.ast;

import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;

public class TransformedWhileStatementAst extends WhileStatementAst {

	public TransformedWhileStatementAst(ExpressionAst cond, StatementAst body) {
		super(cond, body);
	}
	
	public WhileStatementAst with(ExpressionAst cond, StatementAst body) {
		if (super.with(cond, body) ==  this)
			return this;
		
		return new TransformedWhileStatementAst(cond, body);
	}

}
