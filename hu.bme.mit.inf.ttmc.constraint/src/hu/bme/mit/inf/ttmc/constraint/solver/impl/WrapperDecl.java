package hu.bme.mit.inf.ttmc.constraint.solver.impl;


import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface WrapperDecl<DeclType extends Type, Symbol> extends Decl<DeclType> {
	
	public Symbol getSymbol();
	
}
