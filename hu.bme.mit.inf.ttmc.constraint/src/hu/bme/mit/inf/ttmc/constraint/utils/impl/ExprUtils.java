package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeInferrer;

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
	
	public static <T extends Type> Expr<? extends T> cast(final TypeInferrer inferrer, final Expr<? extends Type> expr,
			final Class<T> metaType) {
		if (metaType.isInstance(inferrer.getType(expr))) {
			@SuppressWarnings("unchecked")
			final Expr<? extends T> result = (Expr<? extends T>) expr;
			return result;
		} else {
			throw new ClassCastException("Expression " + expr + " is not of type " + metaType.getName());
		}
	}

}
