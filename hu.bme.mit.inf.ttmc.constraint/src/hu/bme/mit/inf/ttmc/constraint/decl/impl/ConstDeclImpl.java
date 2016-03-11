package hu.bme.mit.inf.ttmc.constraint.decl.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.defaults.AbstractConstDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ConstDeclImpl<DeclType extends Type> extends AbstractConstDecl<DeclType> {

	public ConstDeclImpl(String name, DeclType type) {
		super(name, type);
	}
}
