package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractFuncLitExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class FuncLitExprImpl<ParamType extends Type, ResultType extends Type>
		extends AbstractFuncLitExpr<ParamType, ResultType> {

	public FuncLitExprImpl(ParamDecl<? super ParamType> paramDecl, Expr<? extends ResultType> result) {
		super(paramDecl, result);
	}

}
