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
package hu.bme.mit.theta.analysis.expl;

import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;

import java.util.Collection;
import java.util.Collections;
import java.util.Optional;
import java.util.Set;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Represents an immutable, simple explicit precision that is a set of
 * variables.
 */
public final class ExplPrec implements Prec {

	private final Set<VarDecl<?>> vars;
	private static ExplPrec EMPTY = new ExplPrec(Collections.emptySet());

	private ExplPrec(final Iterable<? extends VarDecl<?>> vars) {
		this.vars = ImmutableSet.copyOf(vars);
	}

	public static ExplPrec empty() {
		return of(Collections.emptySet());
	}

	public static ExplPrec of(final Iterable<? extends VarDecl<?>> vars) {
		checkNotNull(vars);
		if (vars.iterator().hasNext()) {
			return new ExplPrec(vars);
		} else {
			return EMPTY;
		}
	}

	public Set<VarDecl<?>> getVars() {
		return vars;
	}

	public ExplPrec join(final ExplPrec other) {
		checkNotNull(other);
		final Collection<VarDecl<?>> newVars = ImmutableSet.<VarDecl<?>>builder().addAll(vars).addAll(other.vars)
				.build();
		// If no new variable was added, return same instance (immutable)
		if (newVars.size() == this.vars.size()) {
			return this;
		} else if (newVars.size() == other.vars.size()) {
			return other;
		} else {
			return of(newVars);
		}
	}

	public ExplState createState(final Valuation valuation) {
		checkNotNull(valuation);
		final ImmutableValuation.Builder builder = ImmutableValuation.builder();
		for (final VarDecl<?> varDecl : vars) {
			final Optional<? extends LitExpr<?>> eval = valuation.eval(varDecl);
			if (eval.isPresent()) {
				builder.put(varDecl, eval.get());
			}
		}
		return ExplState.of(builder.build());
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).addAll(vars.stream().map(VarDecl::getName))
				.toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ExplPrec) {
			final ExplPrec that = (ExplPrec) obj;
			return this.getVars().equals(that.getVars());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 31 * vars.hashCode();
	}

	@Override
	public Collection<VarDecl<?>> getUsedVars() {
		return vars;
	}
}
