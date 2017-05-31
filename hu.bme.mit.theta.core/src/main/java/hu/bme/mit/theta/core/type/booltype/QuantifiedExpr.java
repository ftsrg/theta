package hu.bme.mit.theta.core.type.booltype;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;

public abstract class QuantifiedExpr implements Expr<BoolType> {

	private final List<ParamDecl<? extends Type>> paramDecls;

	private final Expr<BoolType> op;

	private volatile int hashCode = 0;

	protected QuantifiedExpr(final Iterable<? extends ParamDecl<?>> paramDecls, final Expr<BoolType> op) {
		this.paramDecls = ImmutableList.copyOf(checkNotNull(paramDecls));
		this.op = checkNotNull(op);
	}

	public final List<ParamDecl<?>> getParamDecls() {
		return paramDecls;
	}

	public final Expr<BoolType> getOp() {
		return op;
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + getParamDecls().hashCode();
			result = 31 * result + getOp().hashCode();
			hashCode = result;
		}
		return result;
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

	public abstract QuantifiedExpr withOp(final Expr<BoolType> op);

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
