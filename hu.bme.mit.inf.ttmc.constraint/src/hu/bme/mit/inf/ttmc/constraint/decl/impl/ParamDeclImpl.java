package hu.bme.mit.inf.ttmc.constraint.decl.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.defaults.AbstractParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ParamDeclImpl<DeclType extends Type> extends AbstractParamDecl<DeclType> implements ParamDecl<DeclType> {

	public ParamDeclImpl(String name, DeclType type) {
		super(name, type);
	}
}
