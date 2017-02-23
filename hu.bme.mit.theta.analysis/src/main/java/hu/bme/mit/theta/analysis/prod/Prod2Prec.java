package hu.bme.mit.theta.analysis.prod;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.Product2;

public final class Prod2Prec<P1 extends Prec, P2 extends Prec> extends ProdPrec
		implements Product2<P1, P2> {

	Prod2Prec(final P1 precision1, final P2 precision2) {
		super(ImmutableList.of(precision1, precision2));
	}

	@Override
	public P1 _1() {
		@SuppressWarnings("unchecked")
		final P1 result = (P1) elem(0);
		return result;
	}

	@Override
	public P2 _2() {
		@SuppressWarnings("unchecked")
		final P2 result = (P2) elem(1);
		return result;
	}

}
