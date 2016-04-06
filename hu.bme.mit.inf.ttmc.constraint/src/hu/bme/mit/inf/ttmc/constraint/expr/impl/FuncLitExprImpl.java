package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractFuncLitExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class FuncLitExprImpl<ParamType extends Type, ResultType extends Type>
		extends AbstractFuncLitExpr<ParamType, ResultType> {

	public FuncLitExprImpl(final ConstraintManager manager, final ParamDecl<? super ParamType> paramDecl,
			final Expr<? extends ResultType> result) {
		super(manager, paramDecl, result);
	}

}
