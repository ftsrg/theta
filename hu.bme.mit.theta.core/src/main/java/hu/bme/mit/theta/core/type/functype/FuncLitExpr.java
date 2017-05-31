package hu.bme.mit.theta.core.type.functype;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class FuncLitExpr<ParamType extends Type, ResultType extends Type>
		implements LitExpr<FuncType<ParamType, ResultType>> {

	private static final int HASH_SEED = 53;

	private static final String OPERATOR_LABEL = "Func";

	private final ParamDecl<? super ParamType> paramDecl;
	private final Expr<? extends ResultType> result;

	private volatile int hashCode = 0;

	FuncLitExpr(final ParamDecl<? super ParamType> paramDecl, final Expr<? extends ResultType> result) {
		this.paramDecl = checkNotNull(paramDecl);
		this.result = checkNotNull(result);
	}

	public ParamDecl<? super ParamType> getParamDecl() {
		return paramDecl;
	}

	public Expr<? extends ResultType> getResult() {
		return result;
	}

	@Override
	public FuncType<ParamType, ResultType> getType() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		int tmp = hashCode;
		if (tmp == 0) {
			tmp = HASH_SEED;
			tmp = 31 * tmp + paramDecl.hashCode();
			tmp = 31 * tmp + result.hashCode();
			hashCode = tmp;
		}
		return tmp;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FuncLitExpr) {
			final FuncLitExpr<?, ?> that = (FuncLitExpr<?, ?>) obj;
			return this.getParamDecl().equals(that.getParamDecl()) && this.getResult().equals(that.getResult());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(OPERATOR_LABEL);
		sb.append("(");
		sb.append(paramDecl);
		sb.append(" -> ");
		sb.append(result);
		sb.append(")");
		return sb.toString();
	}

}
