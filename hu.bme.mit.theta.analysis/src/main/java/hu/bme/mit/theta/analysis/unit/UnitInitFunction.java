package hu.bme.mit.theta.analysis.unit;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.InitFunction;

final class UnitInitFunction implements InitFunction<UnitState, UnitPrec> {

	private static final UnitInitFunction INSTANCE = new UnitInitFunction();
	private static final Collection<UnitState> RESULT = ImmutableList.of(UnitState.getInstance());

	private UnitInitFunction() {
	}

	public static UnitInitFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<UnitState> getInitStates(final UnitPrec prec) {
		checkNotNull(prec);
		return RESULT;
	}

}
