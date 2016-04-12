package hu.bme.mit.inf.ttmc.core.solver.impl;

import hu.bme.mit.inf.ttmc.core.expr.Expr;

public interface TermWrapper<Term> {

	public Expr<?> wrap(final Term term);
	
}
