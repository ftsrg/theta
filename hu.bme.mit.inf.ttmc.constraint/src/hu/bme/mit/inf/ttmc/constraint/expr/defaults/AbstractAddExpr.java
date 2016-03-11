package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableMultiset;

import hu.bme.mit.inf.ttmc.constraint.expr.AddExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractAddExpr<ExprType extends ClosedUnderAdd> extends AbstractMultiaryExpr<ExprType, ExprType>
		implements AddExpr<ExprType> {

	private static final String OPERATOR = "Add";

	public AbstractAddExpr(final Collection<? extends Expr<? extends ExprType>> ops) {
		super(ImmutableMultiset.copyOf(checkNotNull(ops)));
	}

	@Override
	public final AddExpr<ExprType> withOps(final Collection<? extends Expr<? extends ExprType>> ops) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 73;
	}

}
