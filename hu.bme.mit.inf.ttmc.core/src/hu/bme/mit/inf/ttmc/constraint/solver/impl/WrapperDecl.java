package hu.bme.mit.inf.ttmc.constraint.solver.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface WrapperDecl<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>, Symbol>
		extends Decl<DeclType, DeclKind> {

	public Symbol getSymbol();

}
