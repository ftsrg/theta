package hu.bme.mit.theta.core.model.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
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
import java.util.StringJoiner;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.Exprs;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;

public final class Valuation implements Assignment {

	private static final int HASH_SEED = 5743;

	private volatile int hashCode = 0;

	private final Map<VarDecl<? extends Type>, LitExpr<?>> declToExpr;

	private volatile Expr<? extends BoolType> expr = null;

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
	public Collection<? extends VarDecl<? extends Type>> getDecls() {
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
	public Expr<? extends BoolType> toExpr() {

		Expr<? extends BoolType> result = expr;

		if (result == null) {

			final List<Expr<? extends BoolType>> ops = new ArrayList<>(declToExpr.size());
			for (final Entry<VarDecl<? extends Type>, LitExpr<?>> entry : declToExpr.entrySet()) {
				ops.add(Exprs.Eq(entry.getKey().getRef(), entry.getValue()));
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
		final StringJoiner sj = new StringJoiner(", ", "Assignment(", ")");
		for (final VarDecl<?> decl : getDecls()) {
			final StringBuilder sb = new StringBuilder();
			sb.append(decl.getName());
			sb.append(" <- ");
			final Optional<?> val = eval(decl);
			assert val.isPresent();
			sb.append(val.get());
			sj.add(sb);
		}
		return sj.toString();
	}

	public static final class Builder implements Assignment {
		private final Map<VarDecl<? extends Type>, LitExpr<?>> declToExpr;
		private boolean built;

		private Builder() {
			this.declToExpr = new HashMap<>();
			this.built = false;
		}

		private Builder(final Map<VarDecl<? extends Type>, LitExpr<?>> declToExpr) {
			this.declToExpr = new HashMap<>(declToExpr);
		}

		public Builder put(final VarDecl<?> decl, final LitExpr<?> value) {
			checkArgument(value.getType().isLeq(decl.getType()));
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
		public Expr<? extends BoolType> toExpr() {
			throw new UnsupportedOperationException();
		}

	}
}
