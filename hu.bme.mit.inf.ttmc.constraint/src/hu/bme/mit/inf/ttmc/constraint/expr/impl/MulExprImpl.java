package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableMultiset;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.MulExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;

public class MulExprImpl<ExprType extends ClosedUnderMul> extends AbstractMultiaryExpr<ExprType, ExprType> implements MulExpr<ExprType> {

	private static final String OPERATOR = "Mul";
		
	public MulExprImpl(final Collection<? extends Expr<? extends ExprType>> ops) {
		super(ImmutableMultiset.copyOf(checkNotNull(ops)));
	}
	
	@Override
	public MulExpr<ExprType> withOps(Collection<? extends Expr<? extends ExprType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new MulExprImpl<>(ops);
		}
	}
	
	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 89;
	}

}
