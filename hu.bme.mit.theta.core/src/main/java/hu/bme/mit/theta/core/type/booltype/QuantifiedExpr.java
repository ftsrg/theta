package hu.bme.mit.theta.core.type.booltype;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.utils.TypeUtils;

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
	public final BoolType getType() {
		return Bool();
	}

	@Override
	public List<Expr<BoolType>> getOps() {
		return ImmutableList.of(op);
	}

	@Override
	public Expr<BoolType> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.size() == 1);
		final Expr<BoolType> newOp = TypeUtils.cast(ops.get(0), Bool());
		return with(newOp);
	}

	@Override
	public int getArity() {
		return 1;
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

	public abstract QuantifiedExpr with(final Expr<BoolType> op);

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
