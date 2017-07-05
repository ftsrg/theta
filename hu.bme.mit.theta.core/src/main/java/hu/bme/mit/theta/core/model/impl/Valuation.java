package hu.bme.mit.theta.core.model.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * Implementation of a valuation, which is a special type of assignment, mapping
 * variable declarations to literal expressions.
 */
public final class Valuation implements Substitution {

	private static final int HASH_SEED = 5743;

	private volatile int hashCode = 0;

	private final Map<VarDecl<?>, LitExpr<?>> declToExpr;

	private volatile Expr<BoolType> expr = null;

	private Valuation(final Builder builder) {
		this.declToExpr = builder.declToExpr;
	}

	public static Builder builder() {
		return new Builder();
	}

	public Builder transform() {
		return new Builder(declToExpr);
	}

	@Override
	public Collection<VarDecl<?>> getDecls() {
		return Collections.unmodifiableCollection(declToExpr.keySet());
	}

	@Override
	public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
		checkNotNull(decl);
		assert (decl instanceof VarDecl<?>);

		if (declToExpr.containsKey(decl)) {
			@SuppressWarnings("unchecked")
			final LitExpr<DeclType> val = (LitExpr<DeclType>) declToExpr.get(decl);
			return Optional.of(val);
		}

		return Optional.empty();
	}

	@Override
	public Expr<BoolType> toExpr() {

		Expr<BoolType> result = expr;

		if (result == null) {

			final List<Expr<BoolType>> ops = new ArrayList<>(declToExpr.size());
			for (final Entry<VarDecl<?>, LitExpr<?>> entry : declToExpr.entrySet()) {
				ops.add(Eq(entry.getKey().getRef(), entry.getValue()));
			}
			if (ops.size() == 0) {
				result = True();
			} else if (ops.size() == 1) {
				result = ops.get(0);
			} else {
				result = And(ops);
			}
			expr = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof Valuation) {
			final Valuation that = (Valuation) obj;
			return this.declToExpr.equals(that.declToExpr);
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + declToExpr.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("Valuation")
				.addAll(declToExpr.entrySet(), e -> e.getKey().getName() + " <- " + e.getValue()).toString();
	}

	public static final class Builder implements Substitution {
		private final Map<VarDecl<?>, LitExpr<?>> declToExpr;
		private boolean built;

		private Builder() {
			this.declToExpr = new HashMap<>();
			this.built = false;
		}

		private Builder(final Map<VarDecl<?>, LitExpr<?>> declToExpr) {
			this.declToExpr = new HashMap<>(declToExpr);
		}

		public Builder put(final VarDecl<?> decl, final LitExpr<?> value) {
			checkArgument(value.getType().equals(decl.getType()));
			checkState(!built);

			declToExpr.put(decl, value);
			return this;
		}

		public Builder remove(final VarDecl<?> decl) {
			checkState(!built);
			declToExpr.remove(decl);
			return this;
		}

		public Valuation build() {
			checkState(!built);
			built = true;
			return new Valuation(this);
		}

		@Override
		public Collection<? extends Decl<?>> getDecls() {
			throw new UnsupportedOperationException();
		}

		@Override
		public <DeclType extends Type> Optional<? extends Expr<DeclType>> eval(final Decl<DeclType> decl) {
			checkNotNull(decl);
			assert (decl instanceof VarDecl<?>);

			if (declToExpr.containsKey(decl)) {
				@SuppressWarnings("unchecked")
				final LitExpr<DeclType> val = (LitExpr<DeclType>) declToExpr.get(decl);
				return Optional.of(val);
			}

			return Optional.empty();
		}

		@Override
		public Expr<BoolType> toExpr() {
			throw new UnsupportedOperationException();
		}

	}
}
