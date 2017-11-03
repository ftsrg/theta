/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
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

import hu.bme.mit.theta.analysis.Prec;
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
public final class PredPrec implements Prec {

	private final Map<Expr<BoolType>, Expr<BoolType>> predToNegMap;
	private final Solver solver;

	public static PredPrec create(final Solver solver) {
		return new PredPrec(Collections.emptySet(), solver);
	}

	public static PredPrec create(final Iterable<Expr<BoolType>> preds, final Solver solver) {
		return new PredPrec(preds, solver);
	}

	public static PredPrec create(final Expr<BoolType> pred, final Solver solver) {
		return new PredPrec(Collections.singleton(pred), solver);
	}

	private PredPrec(final Iterable<Expr<BoolType>> preds, final Solver solver) {
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

				boolean ponValid;
				boolean negValid;
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

	public PredPrec join(final PredPrec other) {
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
		return Utils.lispStringBuilder(getClass().getSimpleName()).addAll(predToNegMap.keySet()).toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof PredPrec) {
			final PredPrec that = (PredPrec) obj;
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
