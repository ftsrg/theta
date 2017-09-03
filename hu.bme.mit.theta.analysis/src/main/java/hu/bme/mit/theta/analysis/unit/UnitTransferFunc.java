package hu.bme.mit.theta.analysis.unit;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransferFunc;

final class UnitTransferFunc implements TransferFunc<UnitState, Action, UnitPrec> {

	private static final UnitTransferFunc INSTANCE = new UnitTransferFunc();
	private static final Collection<UnitState> RESULT = ImmutableList.of(UnitState.getInstance());

	private UnitTransferFunc() {
	}

	public static UnitTransferFunc getInstance() {
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
