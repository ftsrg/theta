package hu.bme.mit.inf.ttmc.formalism.common;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.model.Assignment;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public final class Valuation implements Assignment {

	private final Collection<VarDecl<? extends Type>> decls;
	private final Map<VarDecl<? extends Type>, LitExpr<?>> declToExpr;

	private volatile Expr<? extends BoolType> expr = null;

	private Valuation(final Map<VarDecl<? extends Type>, LitExpr<?>> declToExpr) {
		this.declToExpr = declToExpr;
		this.decls = declToExpr.keySet();
	}

	@Override
	public Collection<? extends VarDecl<? extends Type>> getDecls() {
		return decls;
	}

	@Override
	public <DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> Optional<LitExpr<DeclType>> eval(final Decl<DeclType, DeclKind> decl) {
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
			for (final VarDecl<? extends Type> decl : declToExpr.keySet()) {
				ops.add(Exprs.Eq(decl.getRef(), declToExpr.get(decl)));
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

	public static final class Builder {
		private final Map<VarDecl<? extends Type>, LitExpr<?>> declToExpr;

		public Builder() {
			this.declToExpr = new HashMap<>();
		}

		public Builder put(final VarDecl<? extends Type> decl, final LitExpr<? extends Type> lit) {
			declToExpr.put(decl, lit);
			return this;
		}

		public Valuation build() {
			return new Valuation(declToExpr);
		}

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

	private volatile int hashCode = 0;

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = 31 * result + declToExpr.hashCode();
			hashCode = result;
		}
		return result;
	}
}
