package hu.bme.mit.inf.ttmc.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;
import java.util.StringJoiner;

import hu.bme.mit.inf.ttmc.analysis.ExprState;
import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.model.Assignment;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class ExplState implements ExprState, Assignment {

	private static final int HASH_SEED = 6659;

	private final Valuation values;

	private volatile int hashCode;

	private ExplState(final Valuation values) {
		this.values = checkNotNull(values);
	}

	public static ExplState create(final Valuation values) {
		return new ExplState(values);
	}

	public Collection<? extends VarDecl<? extends Type>> getVars() {
		return values.getDecls();
	}

	public <ExprType extends Type> LitExpr<ExprType> getValue(final VarDecl<ExprType> varDecl) {
		return values.eval(varDecl).get();
	}

	@Override
	public Expr<? extends BoolType> asExpr() {
		return values.toExpr();
	}

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
		final StringBuilder sb = new StringBuilder();
		sb.append("ExplState(");
		final String prefix = sb.toString();
		final String suffix = ")";
		final StringJoiner sj = new StringJoiner(", ", prefix, suffix);
		for (final VarDecl<? extends Type> varDecl : values.getDecls()) {
			sj.add(varDecl.getName() + " = " + getValue(varDecl));
		}
		return sj.toString();
	}

	@Override
	public Collection<? extends Decl<?, ?>> getDecls() {
		return values.getDecls();
	}

	@Override
	public <DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> Optional<LitExpr<DeclType>> eval(final Decl<DeclType, DeclKind> decl) {
		return values.eval(decl);
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		return asExpr();
	}
}
