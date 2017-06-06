package hu.bme.mit.theta.analysis.prod;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Product2;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class Prod2State<S1 extends State, S2 extends State> extends ProdState implements Product2<S1, S2> {

	Prod2State(final S1 state1, final S2 state2) {
		super(ImmutableList.of(state1, state2));
	}

	////

	@Override
	public S1 _1() {
		@SuppressWarnings("unchecked")
		final S1 result = (S1) elem(0);
		return result;
	}

	@Override
	public S2 _2() {
		@SuppressWarnings("unchecked")
		final S2 result = (S2) elem(1);
		return result;
	}

	////

	public <S extends State> Prod2State<S, S2> with1(final S state) {
		return ProdState.of(state, _2());
	}

	public <S extends State> Prod2State<S1, S> with2(final S state) {
		return ProdState.of(_1(), state);
	}

	////

	@Override
	public Expr<BoolType> toExpr() {
		if (_1() instanceof ExprState && _2() instanceof ExprState) {
			final ExprState exprState1 = (ExprState) _1();
			final ExprState exprState2 = (ExprState) _2();
			return And(exprState1.toExpr(), exprState2.toExpr());
		} else {
			throw new UnsupportedOperationException();
		}
	}

}
