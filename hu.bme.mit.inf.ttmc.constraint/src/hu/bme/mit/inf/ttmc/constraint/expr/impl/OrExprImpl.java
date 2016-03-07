package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.OrExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class OrExprImpl extends AbstractMultiaryExpr<BoolType, BoolType> implements OrExpr {

	private static final String OPERATOR = "Or";
		
	public OrExprImpl(final Collection<? extends Expr<? extends BoolType>> ops) {
		super(ImmutableSet.copyOf(checkNotNull(ops)));
	}
	
	@Override
	public OrExpr withOps(Collection<? extends Expr<? extends BoolType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new OrExprImpl(ops);
		}
	}

	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected int getHashSeed() {
		return 131;
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
