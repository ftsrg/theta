package hu.bme.mit.inf.ttmc.constraint.solver.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;

public interface TermWrapper<Term> {

	public Expr<?> wrap(final Term term);
	
}
