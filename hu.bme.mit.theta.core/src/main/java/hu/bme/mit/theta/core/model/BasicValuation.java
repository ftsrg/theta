package hu.bme.mit.theta.core.model;

import static com.google.common.base.Preconditions.checkState;

import java.util.Collection;
import java.util.Collections;
import java.util.Optional;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class BasicValuation implements Valuation {
	private static final int HASH_SEED = 4019;
	private final MutableValuation val;
	private final Collection<? extends Decl<?>> decls;
	private volatile Expr<BoolType> expr = null;

	private BasicValuation(final Builder builder) {
		this.val = builder.val;
		this.decls = Collections.unmodifiableCollection(this.val.getDecls());
	}

	public static BasicValuation copyOf(final Valuation val) {
		final Builder builder = builder();
		for (final Decl<?> decl : val.getDecls()) {
			builder.put(decl, val.eval(decl).get());
		}
		return builder.build();
	}

	@Override
	public Collection<? extends Decl<?>> getDecls() {
		return decls;
	}

	@Override
	public Expr<BoolType> toExpr() {
		Expr<BoolType> result = expr;
		if (result == null) {
			result = val.toExpr();
			expr = result;
		}
		return result;
	}

	@Override
	public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
		return val.eval(decl);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof BasicValuation) {
			final BasicValuation that = (BasicValuation) obj;
			return this.val.equals(that.val);
		} else {
			return false;
		}
	}

	private volatile int hashCode = 0;

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + val.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public String toString() {
		return val.toString();
	}

	public static Builder builder() {
		return new Builder();
	}

	public final static class Builder {
		private final MutableValuation val;
		private boolean built;

		private Builder() {
			this.val = new MutableValuation();
			this.built = false;
		}

		public Builder put(final Decl<?> decl, final LitExpr<?> value) {
			checkState(!built);
			val.put(decl, value);
			return this;
		}

		public BasicValuation build() {
			this.built = true;
			return new BasicValuation(this);
		}

	}
}
