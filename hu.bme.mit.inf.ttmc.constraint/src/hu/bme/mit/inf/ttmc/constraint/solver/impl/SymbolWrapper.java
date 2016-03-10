package hu.bme.mit.inf.ttmc.constraint.solver.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;

public interface SymbolWrapper<Symbol> {

	public ConstDecl<?> wrap(final Symbol symbol);
	
}
