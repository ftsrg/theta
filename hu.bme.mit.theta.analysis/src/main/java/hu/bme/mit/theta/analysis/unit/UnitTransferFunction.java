package hu.bme.mit.theta.analysis.unit;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransferFunction;

final class UnitTransferFunction implements TransferFunction<UnitState, Action, UnitPrec> {

	private static final UnitTransferFunction INSTANCE = new UnitTransferFunction();
	private static final Collection<UnitState> RESULT = ImmutableList.of(UnitState.getInstance());

	private UnitTransferFunction() {
	}

	public static UnitTransferFunction getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<UnitState> getSuccStates(final UnitState state, final Action action, final UnitPrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);
		return RESULT;
	}

}
