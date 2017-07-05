package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.ToStringBuilder;
import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class ExplState implements ExprState, Substitution {

	private static final int HASH_SEED = 6659;

	private final Valuation values;

	private volatile int hashCode;

	private ExplState(final Valuation values) {
		this.values = checkNotNull(values);
	}

	public static ExplState create(final Valuation values) {
		return new ExplState(values);
	}

	public <ExprType extends Type> LitExpr<ExprType> getValue(final VarDecl<ExprType> varDecl) {
		return values.eval(varDecl).get();
	}

	@Override
	public Collection<? extends VarDecl<?>> getDecls() {
		return values.getDecls();
	}

	public Valuation getValuation() {
		return values;
	}

	@Override
	public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
		return values.eval(decl);
	}

	@Override
	public Expr<BoolType> toExpr() {
		return values.toExpr();
	}

	////

	public boolean isLeq(final ExplState that) {
		if (that.getDecls().size() > this.getDecls().size()) {
			return false;
		}
		for (final VarDecl<?> varDecl : that.getDecls()) {
			if (!this.getDecls().contains(varDecl) || !that.getValue(varDecl).equals(this.getValue(varDecl))) {
				return false;
			}
		}
		return true;
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + values.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ExplState) {
			final ExplState that = (ExplState) obj;
			return this.values.equals(that.values);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final ToStringBuilder builder = ObjectUtils.toStringBuilder(getClass().getSimpleName());
		for (final VarDecl<?> varDecl : values.getDecls()) {
			builder.add(varDecl.getName() + " = " + getValue(varDecl));
		}
		return builder.toString();
	}
}
