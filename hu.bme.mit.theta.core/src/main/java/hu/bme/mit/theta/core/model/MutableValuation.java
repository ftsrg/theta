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
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * Mutable implementation of a valuation.
 */
public final class MutableValuation extends Valuation {
	private static final int HASH_SEED = 2141;
	private final Map<Decl<?>, LitExpr<?>> declToExpr;

	public MutableValuation() {
		// LinkedHashMap is used for deterministic order
		this.declToExpr = new LinkedHashMap<>();
	}

	public static MutableValuation copyOf(final Valuation val) {
		final MutableValuation result = new MutableValuation();
		for (final Decl<?> decl : val.getDecls()) {
			result.put(decl, val.eval(decl).get());
		}
		return result;
	}

	public MutableValuation put(final Decl<?> decl, final LitExpr<?> value) {
		checkArgument(value.getType().equals(decl.getType()), "Type mismatch.");
		declToExpr.put(decl, value);
		return this;
	}

	public MutableValuation remove(final Decl<?> decl) {
		declToExpr.remove(decl);
		return this;
	}

	@Override
	public Collection<? extends Decl<?>> getDecls() {
		return Collections.unmodifiableSet(declToExpr.keySet());
	}

	@Override
	public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
		checkNotNull(decl);
		if (declToExpr.containsKey(decl)) {
			@SuppressWarnings("unchecked")
			final LitExpr<DeclType> val = (LitExpr<DeclType>) declToExpr.get(decl);
			return Optional.of(val);
		}
		return Optional.empty();
	}

	@Override
	public Expr<BoolType> toExpr() {
		final List<Expr<BoolType>> ops = new ArrayList<>(declToExpr.size());
		for (final Entry<Decl<?>, LitExpr<?>> entry : declToExpr.entrySet()) {
			ops.add(Eq(entry.getKey().getRef(), entry.getValue()));
		}
		if (ops.isEmpty()) {
			return True();
		} else if (ops.size() == 1) {
			return ops.get(0);
		} else {
			return And(ops);
		}
	}

	@Override
	public Map<Decl<?>, LitExpr<?>> toMap() {
		return Collections.unmodifiableMap(declToExpr);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof MutableValuation) {
			final MutableValuation that = (MutableValuation) obj;
			return this.declToExpr.equals(that.declToExpr);
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return HASH_SEED * 31 + declToExpr.hashCode();
	}

}
