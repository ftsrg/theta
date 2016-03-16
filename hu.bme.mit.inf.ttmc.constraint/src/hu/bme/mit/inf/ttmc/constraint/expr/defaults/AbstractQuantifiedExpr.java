package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.QuantifiedExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractQuantifiedExpr extends AbstractExpr<BoolType> implements QuantifiedExpr {

	private final List<ParamDecl<? extends Type>> paramDecls;

	private final Expr<? extends BoolType> op;

	private volatile int hashCode = 0;

	protected AbstractQuantifiedExpr(final Collection<? extends ParamDecl<? extends Type>> paramDecls,
			final Expr<? extends BoolType> op) {
		this.paramDecls = ImmutableList.copyOf(checkNotNull(paramDecls));
		this.op = checkNotNull(op);
	}

	@Override
	public final List<ParamDecl<? extends Type>> getParamDecls() {
		return paramDecls;
	}

	@Override
	public final Expr<? extends BoolType> getOp() {
		return op;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = getHashSeed();
			hashCode = 31 * hashCode + getParamDecls().hashCode();
			hashCode = 31 * hashCode + getOp().hashCode();
		}

		return hashCode;
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getOperatorLabel());

		final StringJoiner sj = new StringJoiner(", ", "[", "]");
		for (final ParamDecl<?> varDecl : paramDecls) {
			sj.add(varDecl.toString());
		}
		sb.append(sj.toString());

		sb.append("(");
		sb.append(getOp().toString());
		sb.append(")");

		return sb.toString();
	}

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
