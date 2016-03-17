package hu.bme.mit.inf.ttmc.constraint.decl.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.defaults.AbstractParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ParamDeclImpl<DeclType extends Type> extends AbstractParamDecl<DeclType> {

	public ParamDeclImpl(final ConstraintManager manager, final String name, final DeclType type) {
		super(manager, name, type);
	}
}
