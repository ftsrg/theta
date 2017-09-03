package hu.bme.mit.theta.core.model;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class AbstractModel implements Model {

	@Override
	public final Expr<BoolType> toExpr() {
		final List<Expr<BoolType>> exprs = new ArrayList<>();
		for (final Decl<?> decl : getDecls()) {
			final Expr<BoolType> expr = Eq(decl.getRef(), eval(decl).get());
			exprs.add(expr);
		}
		return And(exprs);
	}

	@Override
	public final String toString() {
		return Utils.toStringBuilder("Model").addAll(getDecls(), d -> d.getName() + " <- " + eval(d)).toString();
	}

}
