package hu.bme.mit.inf.ttmc.constraint.solver.impl;


import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface WrapperExpr<ExprType extends Type, Term> extends Expr<ExprType> {
	
	public Term getTerm();
	
}
