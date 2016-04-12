package hu.bme.mit.inf.ttmc.core.solver.impl;


import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface WrapperExpr<ExprType extends Type, Term> extends Expr<ExprType> {
	
	public Term getTerm();
	
}
