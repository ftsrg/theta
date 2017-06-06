package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;

final class AtomCollector {

	private AtomCollector() {
	}

	private static final Collection<Class<?>> CONNECTIVES = ImmutableSet.<Class<?>>builder()

			.add(NotExpr.class)

			.add(ImplyExpr.class)

			.add(IffExpr.class)

			.add(AndExpr.class)

			.add(OrExpr.class)

			// .add(IteExpr.class)

			.add(PrimeExpr.class)

			.build();

	public static void collectAtoms(final Expr<BoolType> expr, final Collection<Expr<BoolType>> atoms) {
		if (CONNECTIVES.contains(expr.getClass())) {
			expr.getOps().stream().forEach(op -> collectAtoms(TypeUtils.cast(op, Bool()), atoms));
		} else {
			atoms.add(expr);
		}
	}

}
