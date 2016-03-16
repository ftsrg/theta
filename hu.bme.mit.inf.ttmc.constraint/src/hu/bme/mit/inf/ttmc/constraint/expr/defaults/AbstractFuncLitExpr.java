package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractFuncLitExpr<ParamType extends Type, ResultType extends Type>
		extends AbstractExpr<FuncType<ParamType, ResultType>> implements FuncLitExpr<ParamType, ResultType> {

	private static final int HASH_SEED = 53;

	private static final String OPERATOR_LABEL = "Func";

	private final ParamDecl<? super ParamType> paramDecl;
	private final Expr<? extends ResultType> result;

	private volatile int hashCode = 0;

	public AbstractFuncLitExpr(final ParamDecl<? super ParamType> paramDecl, final Expr<? extends ResultType> result) {
		this.paramDecl = checkNotNull(paramDecl);
		this.result = checkNotNull(result);
	}

	@Override
	public final ParamDecl<? super ParamType> getParamDecl() {
		return paramDecl;
	}

	@Override
	public final Expr<? extends ResultType> getResult() {
		return result;
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = HASH_SEED;
			hashCode = 31 * hashCode + paramDecl.hashCode();
			hashCode = 31 * hashCode + result.hashCode();
		}

		return hashCode;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FuncLitExpr<?, ?>) {
			final FuncLitExpr<?, ?> that = (FuncLitExpr<?, ?>) obj;
			return this.getParamDecl().equals(that.getParamDecl()) && this.getResult().equals(that.getResult());
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(OPERATOR_LABEL);
		sb.append(paramDecl);
		sb.append(" -> ");
		sb.append(result);
		sb.append(")");
		return sb.toString();
	}

}
