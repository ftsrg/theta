package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableMultiset;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.MulExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractMulExpr<ExprType extends ClosedUnderMul> extends AbstractMultiaryExpr<ExprType, ExprType> implements MulExpr<ExprType> {

	private static final String OPERATOR = "Mul";
		
	public AbstractMulExpr(final Collection<? extends Expr<? extends ExprType>> ops) {
		super(ImmutableMultiset.copyOf(checkNotNull(ops)));
	}
	
	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 89;
	}
	

	@Override
	public final MulExpr<ExprType> withOps(Collection<? extends Expr<? extends ExprType>> ops) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
