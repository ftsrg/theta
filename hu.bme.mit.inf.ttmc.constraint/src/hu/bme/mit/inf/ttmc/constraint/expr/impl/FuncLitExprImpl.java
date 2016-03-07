package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class FuncLitExprImpl<ParamType extends Type, ResultType extends Type>
		extends AbstractExpr<FuncType<ParamType, ResultType>> implements FuncLitExpr<ParamType, ResultType> {

	private final ParamDecl<? super ParamType> paramDecl;
	private final Expr<? extends ResultType> result;

	public FuncLitExprImpl(final ParamDecl<? super ParamType> paramDecl, final Expr<? extends ResultType> result) {
		this.paramDecl = checkNotNull(paramDecl);
		this.result = checkNotNull(result);
	}

	@Override
	public ParamDecl<? super ParamType> getParamDecl() {
		return paramDecl;
	}

	@Override
	public Expr<? extends ResultType> getResult() {
		return result;
	}

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	@Override
	public boolean equals(Object obj) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Func");
		sb.append(paramDecl);
		sb.append(" -> ");
		sb.append(result);
		sb.append(")");
		return sb.toString();
	}

	@Override
	protected int getHashSeed() {
		return 53;
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
