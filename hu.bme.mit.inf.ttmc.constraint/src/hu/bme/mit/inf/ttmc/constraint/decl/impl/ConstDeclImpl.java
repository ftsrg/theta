package hu.bme.mit.inf.ttmc.constraint.decl.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.defaults.AbstractConstDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ConstDeclImpl<DeclType extends Type> extends AbstractConstDecl<DeclType> {

	public ConstDeclImpl(final ConstraintManager manager, final String name, final DeclType type) {
		super(manager, name, type);
	}
}
