package hu.bme.mit.inf.ttmc.formalism.common;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.StringJoiner;

import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.model.Assignment;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

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
	public <DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> Optional<LitExpr<DeclType>> eval(
			final Decl<DeclType, DeclKind> decl) {
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
				result = Exprs.True();
			} else if (ops.size() == 1) {
				result = ops.get(0);
			} else {
				result = Exprs.And(ops);
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

	public static final class Builder {
		private final Map<VarDecl<? extends Type>, LitExpr<?>> declToExpr;

		private Builder() {
			this.declToExpr = new HashMap<>();
		}

		private Builder(final Map<VarDecl<? extends Type>, LitExpr<?>> declToExpr) {
			this.declToExpr = new HashMap<>(declToExpr);
		}

		public Builder put(final VarDecl<?> decl, final LitExpr<?> value) {
			checkArgument(value.getType().isLeq(decl.getType()));

			declToExpr.put(decl, value);
			return this;
		}

		public Builder remove(final VarDecl<?> decl) {
			declToExpr.remove(decl);
			return this;
		}

		public Builder project(final Collection<? extends VarDecl<?>> decls) {
			for (final VarDecl<?> decl : decls) {
				remove(decl);
			}
			return this;
		}

		public Valuation build() {
			return new Valuation(this);
		}

	}
}
