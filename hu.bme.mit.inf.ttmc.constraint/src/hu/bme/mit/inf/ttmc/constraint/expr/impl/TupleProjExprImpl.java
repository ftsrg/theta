package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.TupleProjExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractUnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.TupleType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class TupleProjExprImpl
		extends AbstractUnaryExpr<TupleType, Type> implements TupleProjExpr {

	private final int index;

	private volatile int hashCode = 0;

	public TupleProjExprImpl(final Expr<? extends TupleType> op, final int index) {
		super(op);
		checkArgument(index > 0);
		this.index = index;
	}

	@Override
	public int getIndex() {
		return index;
	}
	
	@Override
	public UnaryExpr<TupleType, Type> withOp(Expr<? extends TupleType> op) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = super.hashCode();
			hashCode = 31 * hashCode + index;
		}

		return hashCode;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final TupleProjExprImpl that = (TupleProjExprImpl) obj;
			return this.index == that.index && this.getOp().equals(that.getOp());
		} else {
			return false;
		}
	}

	@Override
	protected final String getOperatorString() {
		return "." + getIndex();
	}

	@Override
	protected int getHashSeed() {
		return 179;
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
