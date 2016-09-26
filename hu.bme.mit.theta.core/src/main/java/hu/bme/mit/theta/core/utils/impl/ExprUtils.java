package hu.bme.mit.theta.core.utils.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.AndExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.expr.NotExpr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.CnfCheckerVisitor.CNFStatus;

public class ExprUtils {

	private ExprUtils() {
	}

	public static CnfTransformation createCNFTransformation() {
		return new CnfTransformation();
	}

	public static Collection<Expr<? extends BoolType>> getConjuncts(final Expr<? extends BoolType> expr) {
		checkNotNull(expr);

		if (expr instanceof AndExpr) {
			final AndExpr andExpr = (AndExpr) expr;
			return andExpr.getOps().stream().map(e -> getConjuncts(e)).flatMap(c -> c.stream())
					.collect(Collectors.toSet());
		} else {
			return Collections.singleton(expr);
		}
	}

	public static <T extends Type> Expr<? extends T> cast(final Expr<? extends Type> expr, final Class<T> metaType) {
		checkNotNull(expr);
		checkNotNull(metaType);

		if (metaType.isInstance(expr.getType())) {
			@SuppressWarnings("unchecked")
			final Expr<? extends T> result = (Expr<? extends T>) expr;
			return result;
		} else {
			throw new ClassCastException("The type of expression " + expr + " is not of type " + metaType.getName());
		}
	}

	public static void collectVars(final Expr<? extends Type> expr,
			final Collection<VarDecl<? extends Type>> collectTo) {
		expr.accept(VarCollectorExprVisitor.getInstance(), collectTo);
	}

	public static void collectVars(final Collection<? extends Expr<? extends Type>> exprs,
			final Collection<VarDecl<? extends Type>> collectTo) {
		for (final Expr<? extends Type> expr : exprs) {
			collectVars(expr, collectTo);
		}
	}

	public static Set<VarDecl<? extends Type>> getVars(final Expr<? extends Type> expr) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		collectVars(expr, vars);
		return vars;
	}

	public static Set<VarDecl<? extends Type>> getVars(final Collection<? extends Expr<? extends Type>> exprs) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		collectVars(exprs, vars);
		return vars;
	}

	public static boolean isExprCNF(final Expr<? extends BoolType> expr) {
		return expr.accept(new CnfCheckerVisitor(), CNFStatus.START);
	}

	@SuppressWarnings("unchecked")
	public static Expr<? extends BoolType> eliminateITE(final Expr<? extends BoolType> expr) {
		return (Expr<? extends BoolType>) expr.accept(new ItePropagatorVisitor(new ItePusherVisitor()), null)
				.accept(new IteRemoverVisitor(), null);
	}

	public static void collectAtoms(final Expr<? extends BoolType> expr,
			final Collection<Expr<? extends BoolType>> collectTo) {
		expr.accept(new AtomCollectorVisitor(), collectTo);
	}

	@SuppressWarnings("unchecked")
	public static <ExprType extends Type> Expr<? extends ExprType> simplify(final Expr<? extends ExprType> expr,
			final Assignment assignment) {
		return (Expr<? extends ExprType>) expr.accept(new ExprSimplifierVisitor(), assignment);
	}

	public static <ExprType extends Type> Expr<? extends ExprType> simplify(final Expr<? extends ExprType> expr) {
		return simplify(expr, AssignmentImpl.empty());
	}

	@SuppressWarnings("unchecked")
	public static <ExprType extends Type> LitExpr<? extends ExprType> evaluate(final Expr<? extends ExprType> expr,
			final Assignment assignment) {
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

	public static Expr<? extends BoolType> ponate(final Expr<? extends BoolType> expr) {
		if (expr instanceof NotExpr) {
			final NotExpr notExpr = (NotExpr) expr;
			return ponate(notExpr.getOp());
		} else {
			return expr;
		}
	}
}
