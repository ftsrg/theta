package hu.bme.mit.inf.ttmc.solver.impl;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;

public interface SymbolWrapper<Symbol> {

	public ConstDecl<?> wrap(final Symbol symbol);
	
}
