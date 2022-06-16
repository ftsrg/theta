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
package hu.bme.mit.theta.core.model;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Map;
import java.util.Optional;

import com.google.common.collect.ImmutableMap;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * Basic, immutable implementation of a valuation. The inner builder class can
 * be used to create a new instance.
 */
public final class ImmutableValuation extends Valuation {
	private final Map<Decl<?>, LitExpr<?>> declToExpr;
	private volatile Expr<BoolType> expr = null;

	private static final class LazyHolder {
		private static final ImmutableValuation EMPTY = new Builder().build();
	}

	private ImmutableValuation(final Builder builder) {
		declToExpr = builder.builder.build();
	}

	public static ImmutableValuation copyOf(final Valuation val) {
		if (val instanceof ImmutableValuation) {
			return (ImmutableValuation) val;
		} else {
			final Builder builder = builder();
			for (final Decl<?> decl : val.getDecls()) {
				builder.put(decl, val.eval(decl).get());
			}
			return builder.build();
		}
	}

	public static ImmutableValuation empty() {
		return LazyHolder.EMPTY;
	}

	@Override
	public Collection<Decl<?>> getDecls() {
		return declToExpr.keySet();
	}

	@Override
	public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
		checkNotNull(decl);
		@SuppressWarnings("unchecked") final LitExpr<DeclType> val = (LitExpr<DeclType>) declToExpr.get(decl);
		return Optional.ofNullable(val);
	}

	@Override
	public Expr<BoolType> toExpr() {
		Expr<BoolType> result = expr;
		if (result == null) {
			result = super.toExpr();
			expr = result;
		}
		return result;
	}

	@Override
	public Map<Decl<?>, LitExpr<?>> toMap() {
		return declToExpr;
	}

	public static Builder builder() {
		return new Builder();
	}

	public final static class Builder {
		private final ImmutableMap.Builder<Decl<?>, LitExpr<?>> builder;

		private Builder() {
			builder = ImmutableMap.builder();
		}

		public Builder put(final Decl<?> decl, final LitExpr<?> value) {
			checkArgument(value.getType().equals(decl.getType()), "Type mismatch.");
			builder.put(decl, value);
			return this;
		}

		public ImmutableValuation build() {
			return new ImmutableValuation(this);
		}

	}

}
