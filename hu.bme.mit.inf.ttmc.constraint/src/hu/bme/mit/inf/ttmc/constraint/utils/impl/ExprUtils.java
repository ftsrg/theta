package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprCNFCheckerVisitor.CNFStatus;

public class ExprUtils {

	private ExprUtils() {
	}

	public static Collection<Expr<? extends BoolType>> getConjuncts(final Expr<? extends BoolType> expr) {
		if (expr instanceof AndExpr) {
			final AndExpr andExpr = (AndExpr) expr;
			return andExpr.getOps().stream().map(e -> getConjuncts(e)).flatMap(c -> c.stream())
					.collect(Collectors.toSet());
		} else {
			return Collections.singleton(expr);
		}
	}

	public static <T extends Type> Expr<? extends T> cast(final Expr<? extends Type> expr, final Class<T> metaType) {
		if (metaType.isInstance(expr.getType())) {
			@SuppressWarnings("unchecked")
			final Expr<? extends T> result = (Expr<? extends T>) expr;
			return result;
		} else {
			throw new ClassCastException("Expression " + expr + " is not of type " + metaType.getName());
		}
	}

	public static boolean isExprCNF(final Expr<? extends BoolType> expr) {
		return expr.accept(new ExprCNFCheckerVisitor(), CNFStatus.START);
	}

	@SuppressWarnings("unchecked")
	public static Expr<? extends BoolType> eliminateITE(final Expr<? extends BoolType> expr,
			final ConstraintManager manager) {
		return (Expr<? extends BoolType>) expr
				.accept(new ExprITEPropagatorVisitor(manager, new ExprITEPusherVisitor(manager)), null)
				.accept(new ExprITERemoverVisitor(manager), null);
	}

}
