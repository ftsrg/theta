package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractForallExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ForallExprImpl extends AbstractForallExpr {

	public ForallExprImpl(final ConstraintManager manager,
			final Collection<? extends ParamDecl<? extends Type>> paramDecls, final Expr<? extends BoolType> op) {
		super(manager, paramDecls, op);
	}

}
