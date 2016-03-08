package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public class ExprUtils {

	private ExprUtils() {
	}

	public static Collection<Expr<? extends BoolType>> getConjuncts(Expr<? extends BoolType> expr) {
		if (expr instanceof AndExpr) {
			final AndExpr andExpr = (AndExpr) expr;
			return andExpr.getOps().stream().map(e -> getConjuncts(e)).flatMap(c -> c.stream())
					.collect(Collectors.toSet());
		} else {
			return Collections.singleton(expr);
		}
	}

}
