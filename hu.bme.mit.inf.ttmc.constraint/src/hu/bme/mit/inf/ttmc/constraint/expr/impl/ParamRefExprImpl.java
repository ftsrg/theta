package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ParamRefExprImpl<DeclType extends Type> extends AbstractParamRefExpr<DeclType> {

	public ParamRefExprImpl(final ParamDecl<DeclType> paramDecl) {
		super(paramDecl);
	}

}
