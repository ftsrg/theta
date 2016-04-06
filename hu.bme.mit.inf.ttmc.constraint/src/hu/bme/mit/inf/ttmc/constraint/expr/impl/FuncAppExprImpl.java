package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractFuncAppExpr;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class FuncAppExprImpl<ParamType extends Type, ResultType extends Type>
		extends AbstractFuncAppExpr<ParamType, ResultType> {

	public FuncAppExprImpl(final ConstraintManager manager,
			final Expr<? extends FuncType<? super ParamType, ? extends ResultType>> func,
			final Expr<? extends ParamType> param) {
		super(manager, func, param);
	}

}
