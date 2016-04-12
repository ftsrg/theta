package hu.bme.mit.inf.ttmc.solver.impl;

import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface WrapperDecl<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>, Symbol>
		extends Decl<DeclType, DeclKind> {

	public Symbol getSymbol();

}
