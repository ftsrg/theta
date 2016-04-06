package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ParamRefExprImpl<DeclType extends Type> extends AbstractParamRefExpr<DeclType> {

	public ParamRefExprImpl(final ConstraintManager manager, final ParamDecl<DeclType> paramDecl) {
		super(manager, paramDecl);
	}

}
