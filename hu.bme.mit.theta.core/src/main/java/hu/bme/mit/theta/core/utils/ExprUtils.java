package hu.bme.mit.theta.core.utils;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.utils.IndexedVars.Builder;

public final class ExprUtils {

	private ExprUtils() {
	}

	public static CnfTransformation createCNFTransformation() {
		return new CnfTransformation();
	}

	public static Collection<Expr<BoolType>> getConjuncts(final Expr<BoolType> expr) {
		checkNotNull(expr);

		if (expr instanceof AndExpr) {
			final AndExpr andExpr = (AndExpr) expr;
			return andExpr.getOps().stream().map(e -> getConjuncts(e)).flatMap(c -> c.stream())
					.collect(Collectors.toSet());
		} else {
			return Collections.singleton(expr);
		}
	}

	public static void collectVars(final Expr<?> expr, final Collection<VarDecl<?>> collectTo) {
		if (expr instanceof RefExpr) {
			final RefExpr<?> refExpr = (RefExpr<?>) expr;
			final Decl<?> decl = refExpr.getDecl();
			if (decl instanceof VarDecl) {
				final VarDecl<?> var = (VarDecl<?>) decl;
				collectTo.add(var);
				return;
			}
		}
		expr.getOps().forEach(op -> collectVars(op, collectTo));
	}

	public static void collectVars(final Iterable<? extends Expr<?>> exprs,
			final Collection<VarDecl<? extends Type>> collectTo) {
		exprs.forEach(e -> collectVars(e, collectTo));
	}

	public static Set<VarDecl<?>> getVars(final Expr<?> expr) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		collectVars(expr, vars);
		return vars;
	}

	public static Set<VarDecl<? extends Type>> getVars(final Iterable<? extends Expr<?>> exprs) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		collectVars(exprs, vars);
		return vars;
	}

	public static IndexedVars getVarsIndexed(final Expr<?> expr) {
		final Builder builder = IndexedVars.builder();
		IndexedVarCollector.collectIndexedVars(expr, builder);
		return builder.build();
	}

	public static IndexedVars getVarsIndexed(final Iterable<? extends Expr<?>> exprs) {
		final Builder builder = IndexedVars.builder();
		exprs.forEach(e -> IndexedVarCollector.collectIndexedVars(e, builder));
		return builder.build();
	}

	public static boolean isExprCnf(final Expr<BoolType> expr) {
		return CnfChecker.isCnf(expr);
	}

	public static Expr<BoolType> eliminateIte(final Expr<BoolType> expr) {
		return IteRemover.removeIte(ItePropagator.propagateIte(expr));
	}

	public static void collectAtoms(final Expr<BoolType> expr, final Collection<Expr<BoolType>> collectTo) {
		AtomCollector.collectAtoms(expr, collectTo);
	}

	public static Set<Expr<BoolType>> getAtoms(final Expr<BoolType> expr) {
		final Set<Expr<BoolType>> atoms = new HashSet<>();
		collectAtoms(expr, atoms);
		return atoms;
	}

	public static <ExprType extends Type> Expr<ExprType> simplify(final Expr<ExprType> expr,
			final Assignment assignment) {
		return new ExprSimplifier(assignment).simplify(expr);
	}

	public static List<Expr<?>> simplifyAll(final List<? extends Expr<?>> exprs) {
		final List<Expr<?>> simplifiedArgs = new ArrayList<>();
		for (final Expr<?> expr : exprs) {
			final Expr<?> simplifiedArg = simplify(expr);
			simplifiedArgs.add(simplifiedArg);
		}
		return simplifiedArgs;
	}

	public static <ExprType extends Type> Expr<ExprType> simplify(final Expr<ExprType> expr) {
		return simplify(expr, AssignmentImpl.empty());
	}

	public static <ExprType extends Type> LitExpr<ExprType> evaluate(final Expr<ExprType> expr,
			final Assignment assignment) {
		final Expr<ExprType> simplified = simplify(expr, assignment);
		if (simplified instanceof LitExpr) {
			return (LitExpr<ExprType>) simplified;
		} else {
			throw new RuntimeException("Could not evaluate " + expr + " with assignment " + assignment);
		}
	}

	public static <ExprType extends Type> LitExpr<ExprType> evaluate(final Expr<ExprType> expr) {
		return evaluate(expr, AssignmentImpl.empty());
	}

	public static Expr<BoolType> ponate(final Expr<BoolType> expr) {
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

	public static int size(final Expr<?> expr, final ExprMetrics.ExprMetric metric) {
		return metric.calculate(expr);
	}
}
