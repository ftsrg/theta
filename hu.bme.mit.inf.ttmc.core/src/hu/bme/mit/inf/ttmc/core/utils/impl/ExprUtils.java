package hu.bme.mit.inf.ttmc.core.utils.impl;

import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.model.Assignment;
import hu.bme.mit.inf.ttmc.core.model.impl.AssignmentImpl;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprCNFCheckerVisitor.CNFStatus;

public class ExprUtils {

	private ExprUtils() {
	}

	public static Collection<Expr<? extends BoolType>> getConjuncts(final Expr<? extends BoolType> expr) {
		if (expr instanceof AndExpr) {
			final AndExpr andExpr = (AndExpr) expr;
			return andExpr.getOps().stream().map(e -> getConjuncts(e)).flatMap(c -> c.stream()).collect(Collectors.toSet());
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
			throw new ClassCastException("The type of expression " + expr + " is not of type " + metaType.getName());
		}
	}

	public static boolean isExprCNF(final Expr<? extends BoolType> expr) {
		return expr.accept(new ExprCNFCheckerVisitor(), CNFStatus.START);
	}

	@SuppressWarnings("unchecked")
	public static Expr<? extends BoolType> eliminateITE(final Expr<? extends BoolType> expr) {
		return (Expr<? extends BoolType>) expr.accept(new ExprITEPropagatorVisitor(new ExprITEPusherVisitor()), null).accept(new ExprITERemoverVisitor(), null);
	}

	public static void collectAtoms(final Expr<? extends BoolType> expr, final Collection<Expr<? extends BoolType>> collectTo) {
		expr.accept(new AtomCollectorVisitor(), collectTo);
	}

	@SuppressWarnings("unchecked")
	public static <ExprType extends Type> Expr<? extends ExprType> simplify(final Expr<? extends ExprType> expr, final Assignment assignment) {
		return (Expr<? extends ExprType>) expr.accept(new ExprSimplifierVisitor(), assignment);
	}

	public static <ExprType extends Type> Expr<? extends ExprType> simplify(final Expr<? extends ExprType> expr) {
		return simplify(expr, AssignmentImpl.empty());
	}

	@SuppressWarnings("unchecked")
	public static <ExprType extends Type> LitExpr<? extends ExprType> evaluate(final Expr<? extends ExprType> expr, final Assignment assignment) {
		final Expr<? extends ExprType> simplified = simplify(expr, assignment);
		if (simplified instanceof LitExpr<?>) {
			return (LitExpr<ExprType>) simplified;
		} else {
			throw new RuntimeException("Could not evaluate " + expr + " with assignment " + assignment);
		}
	}

	public static <ExprType extends Type> LitExpr<? extends ExprType> evaluate(final Expr<? extends ExprType> expr) {
		return evaluate(expr, AssignmentImpl.empty());
	}
}
