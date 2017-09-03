package hu.bme.mit.theta.analysis.unit;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.InitFunc;

final class UnitInitFunc implements InitFunc<UnitState, UnitPrec> {

	private static final UnitInitFunc INSTANCE = new UnitInitFunc();
	private static final Collection<UnitState> RESULT = ImmutableList.of(UnitState.getInstance());

	private UnitInitFunc() {
	}

	public static UnitInitFunc getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<UnitState> getInitStates(final UnitPrec prec) {
		checkNotNull(prec);
		return RESULT;
	}

}
