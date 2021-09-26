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

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

/**
 * Represents an immutable, simple predicate precision that is a set of
 * predicates.
 */
public final class PredPrec implements Prec {

	private final Map<Expr<BoolType>, Expr<BoolType>> predToNegMap;

	private PredPrec(final Iterable<Expr<BoolType>> preds) {
		checkNotNull(preds);
		this.predToNegMap = Containers.createMap();

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

	public static PredPrec of(final Iterable<Expr<BoolType>> preds) {
		return new PredPrec(preds);
	}

	// Convenience factory methods

	public static PredPrec of() {
		return new PredPrec(Collections.emptySet());
	}

	public static PredPrec of(final Expr<BoolType> pred) {
		return new PredPrec(Collections.singleton(pred));
	}

	////

	public Set<Expr<BoolType>> getPreds() {
		return Collections.unmodifiableSet(predToNegMap.keySet());
	}

	public Expr<BoolType> negate(final Expr<BoolType> pred) {
		final Expr<BoolType> negated = predToNegMap.get(pred);
		checkArgument(negated != null, "Negated predicate not found");
		return negated;
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

		return of(joinedPreds);
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

	@Override
	public Collection<VarDecl<?>> getUsedVars() {
		return predToNegMap.keySet().stream().map(ExprUtils::getVars).reduce((vars1, vars2) -> Streams.concat(vars1.stream(), vars2.stream()).collect(Collectors.toSet())).orElse(Set.of());
	}
}
