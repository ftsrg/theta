package hu.bme.mit.theta.core.model.impl;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.StringJoiner;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class AbstractModel implements Model {

	@Override
	public final Expr<BoolType> toExpr() {
		final List<Expr<BoolType>> exprs = new ArrayList<>();
		for (final ConstDecl<?> constDecl : getDecls()) {
			final Expr<BoolType> expr = Eq(constDecl.getRef(), eval(constDecl).get());
			exprs.add(expr);
		}
		return And(exprs);
	}

	@Override
	public final String toString() {
		final StringJoiner sj = new StringJoiner(", ", "Model(", ")");
		for (final ConstDecl<?> constDecl : getDecls()) {
			final StringBuilder sb = new StringBuilder();
			sb.append(constDecl.getName());
			sb.append(" <- ");
			final Optional<?> val = eval(constDecl);
			assert val.isPresent();
			sb.append(val.get());
			sj.add(sb);
		}
		return sj.toString();
	}

}
