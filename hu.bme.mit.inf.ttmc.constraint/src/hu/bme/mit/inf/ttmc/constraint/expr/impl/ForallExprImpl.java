package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractForallExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ForallExprImpl extends AbstractForallExpr {

	public ForallExprImpl(Collection<? extends ParamDecl<? extends Type>> paramDecls, Expr<? extends BoolType> op) {
		super(paramDecls, op);
	}

}
