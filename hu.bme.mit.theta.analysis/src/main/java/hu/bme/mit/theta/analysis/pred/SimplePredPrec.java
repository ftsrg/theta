package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

/**
 * Represents an immutable, simple predicate precision that is a set of
 * predicates.
 */
public final class SimplePredPrec implements PredPrec {

	private final Map<Expr<BoolType>, Expr<BoolType>> predToNegMap;
	private final Solver solver;

	public static SimplePredPrec create(final Solver solver) {
		return new SimplePredPrec(Collections.emptySet(), solver);
	}

	public static SimplePredPrec create(final Iterable<Expr<BoolType>> preds, final Solver solver) {
		return new SimplePredPrec(preds, solver);
	}

	public static SimplePredPrec create(final Expr<BoolType> pred, final Solver solver) {
		return new SimplePredPrec(Collections.singleton(pred), solver);
	}

	private SimplePredPrec(final Iterable<Expr<BoolType>> preds, final Solver solver) {
		checkNotNull(preds);
		this.solver = checkNotNull(solver);
		this.predToNegMap = new HashMap<>();

		for (final Expr<BoolType> pred : preds) {
			if (pred instanceof BoolLitExpr) {
				continue;
			}
			final Expr<BoolType> ponatedPred = ExprUtils.ponate(pred);
			if (!this.predToNegMap.containsKey(ponatedPred)) {
				this.predToNegMap.put(ponatedPred, Not(ponatedPred));
			}
		}
	}

	public Solver getSolver() {
		return solver;
	}

	private Expr<BoolType> negate(final Expr<BoolType> pred) {
		final Expr<BoolType> negated = predToNegMap.get(pred);
		checkArgument(negated != null, "Negated predicate not found");
		return negated;
	}

	@Override
	public PredState createState(final Valuation valuation) {
		checkNotNull(valuation);
		final Set<Expr<BoolType>> statePreds = new HashSet<>();

		for (final Expr<BoolType> pred : predToNegMap.keySet()) {
			final Expr<BoolType> simplified = ExprUtils.simplify(pred, valuation);
			if (simplified.equals(True())) {
				statePreds.add(pred);
			} else if (simplified.equals(False())) {
				statePreds.add(negate(pred));
			} else {
				final Expr<BoolType> simplified0 = PathUtils.unfold(simplified, 0);

				boolean ponValid, negValid;
				try (WithPushPop wpp = new WithPushPop(solver)) {
					solver.add(Not(simplified0));
					ponValid = solver.check().isUnsat();
				}
				try (WithPushPop wpp = new WithPushPop(solver)) {
					solver.add(simplified0);
					negValid = solver.check().isUnsat();
				}

				assert !(ponValid && negValid) : "Ponated and negated predicates are both valid";
				if (ponValid) {
					statePreds.add(pred);
				} else if (negValid) {
					statePreds.add(negate(pred));
				}
			}
		}

		return PredState.of(statePreds);
	}

	public SimplePredPrec join(final SimplePredPrec other) {
		checkNotNull(other);
		final Collection<Expr<BoolType>> joinedPreds = ImmutableSet.<Expr<BoolType>>builder()
				.addAll(this.predToNegMap.keySet()).addAll(other.predToNegMap.keySet()).build();
		// If no new predicate was added, return same instance (immutable)
		if (joinedPreds.size() == this.predToNegMap.size()) {
			return this;
		} else if (joinedPreds.size() == other.predToNegMap.size()) {
			return other;
		}

		return create(joinedPreds, solver);
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder(getClass().getSimpleName()).addAll(predToNegMap.keySet()).toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof SimplePredPrec) {
			final SimplePredPrec that = (SimplePredPrec) obj;
			return this.predToNegMap.keySet().equals(that.predToNegMap.keySet());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 31 * predToNegMap.keySet().hashCode();
	}
}
