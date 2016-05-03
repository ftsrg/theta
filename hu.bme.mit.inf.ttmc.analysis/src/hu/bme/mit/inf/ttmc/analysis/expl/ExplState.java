package hu.bme.mit.inf.ttmc.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.StringJoiner;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class ExplState implements State {

	private static final int HASH_SEED = 6659;

	private final Map<VarDecl<? extends Type>, LitExpr<? extends Type>> values;

	private volatile int hashCode;

	private volatile Expr<? extends BoolType> expr = null;

	private ExplState(final Map<VarDecl<? extends Type>, LitExpr<? extends Type>> values) {
		this.values = new HashMap<>(checkNotNull(values));
	}

	public static ExplState create(final Map<VarDecl<? extends Type>, LitExpr<? extends Type>> values) {
		return new ExplState(values);
	}

	public Collection<? extends VarDecl<? extends Type>> getVars() {
		return values.keySet();
	}

	@SuppressWarnings("unchecked")
	public <ExprType extends Type> LitExpr<ExprType> getValue(final VarDecl<ExprType> varDecl) {
		return (LitExpr<ExprType>) values.get(varDecl);
	}

	public Expr<? extends BoolType> asExpr() {
		Expr<? extends BoolType> result = expr;
		if (result == null) {
			final List<EqExpr> ops = new ArrayList<>(values.size());
			for (final VarDecl<? extends Type> varDecl : values.keySet()) {
				ops.add(Exprs.Eq(varDecl.getRef(), values.get(varDecl)));
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
		for (final VarDecl<? extends Type> varDecl : values.keySet()) {
			sj.add(varDecl.getName() + " = " + values.get(varDecl));
		}
		return sj.toString();
	}
}
