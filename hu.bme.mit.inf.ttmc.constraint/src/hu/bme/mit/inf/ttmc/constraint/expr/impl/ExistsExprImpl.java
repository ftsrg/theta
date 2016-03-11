package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractExistsExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ExistsExprImpl extends AbstractExistsExpr {

	public ExistsExprImpl(Collection<? extends ParamDecl<? extends Type>> paramDecls, Expr<? extends BoolType> op) {
		super(paramDecls, op);
	}

}
