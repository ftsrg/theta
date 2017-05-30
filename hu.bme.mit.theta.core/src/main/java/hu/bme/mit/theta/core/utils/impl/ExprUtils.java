package hu.bme.mit.theta.core.utils.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.utils.impl.CnfCheckerVisitor.CNFStatus;
import hu.bme.mit.theta.core.utils.impl.IndexedVars.Builder;

public final class ExprUtils {

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

	public static void collectVars(final Expr<? extends Type> expr,
			final Collection<VarDecl<? extends Type>> collectTo) {
		expr.accept(VarCollectorExprVisitor.getInstance(), collectTo);
	}

	public static void collectVars(final Iterable<? extends Expr<? extends Type>> exprs,
			final Collection<VarDecl<? extends Type>> collectTo) {
		exprs.forEach(e -> collectVars(e, collectTo));
	}

	public static Set<VarDecl<? extends Type>> getVars(final Expr<? extends Type> expr) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		collectVars(expr, vars);
		return vars;
	}

	public static Set<VarDecl<? extends Type>> getVars(final Iterable<? extends Expr<? extends Type>> exprs) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		collectVars(exprs, vars);
		return vars;
	}

	public static IndexedVars getVarsIndexed(final Expr<? extends Type> expr) {
		final Builder builder = IndexedVars.builder();
		expr.accept(IndexedVarCollectorVisitor.getInstance(), builder);
		return builder.build();
	}

	public static IndexedVars getVarsIndexed(final Iterable<? extends Expr<? extends Type>> exprs) {
		final Builder builder = IndexedVars.builder();
		exprs.forEach(e -> e.accept(IndexedVarCollectorVisitor.getInstance(), builder));
		return builder.build();
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

	public static Set<Expr<? extends BoolType>> getAtoms(final Expr<? extends BoolType> expr) {
		final Set<Expr<? extends BoolType>> atoms = new HashSet<>();
		collectAtoms(expr, atoms);
		return atoms;
	}

	@SuppressWarnings("unchecked")
	public static <ExprType extends Type> Expr<? extends ExprType> simplify(final Expr<? extends ExprType> expr,
			final Assignment assignment) {
		return (Expr<? extends ExprType>) expr.accept(new ExprSimplifierVisitor(), assignment);
	}

	public static List<Expr<?>> simplifyAll(final List<? extends Expr<?>> exprs) {
		final List<Expr<?>> simplifiedArgs = new ArrayList<>();
		for (final Expr<?> expr : exprs) {
			final Expr<?> simplifiedArg = simplify(expr);
			simplifiedArgs.add(simplifiedArg);
		}
		return simplifiedArgs;
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

	public static <T extends Type> Expr<T> close(final Expr<T> expr, final Map<VarDecl<?>, ParamDecl<?>> mapping) {
		return ExprClosureHelper.close(expr, mapping);
	}

	public static <T extends Type> Expr<T> applyPrimes(final Expr<T> expr, final VarIndexing indexing) {
		return PrimeApplier.applyPrimes(expr, indexing);
	}

	public static int size(final Expr<? extends Type> expr, final ExprMetrics.ExprMetric metric) {
		return expr.accept(metric, null);
	}
}
