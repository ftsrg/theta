package hu.bme.mit.theta.analysis.prod;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.common.Product3;

public final class Prod3Precision<P1 extends Precision, P2 extends Precision, P3 extends Precision>
		extends ProdPrecision implements Product3<P1, P2, P3> {

	Prod3Precision(final P1 precision1, final P2 precision2, final P3 precision3) {
		super(ImmutableList.of(precision1, precision2, precision3));
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

	@Override
	public P3 _3() {
		@SuppressWarnings("unchecked")
		final P3 result = (P3) elem(2);
		return result;
	}

}
