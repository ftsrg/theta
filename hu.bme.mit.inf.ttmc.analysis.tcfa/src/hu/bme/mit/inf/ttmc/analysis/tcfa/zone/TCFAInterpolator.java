package hu.bme.mit.inf.ttmc.analysis.tcfa.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.tcfa.TCFAAction;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneDomain;
import hu.bme.mit.inf.ttmc.analysis.zone.ZonePrecision;
import hu.bme.mit.inf.ttmc.analysis.zone.ZoneState;

public class TCFAInterpolator {

	private final ZonePrecision precision;

	public TCFAInterpolator(final ZonePrecision precision) {
		this.precision = checkNotNull(precision);
	}

	public List<ZoneState> getInterpolant(final List<? extends TCFAAction> actions) {
		final List<ZoneState> interpolants = new ArrayList<>(actions.size() + 1);

		final List<ZoneState> forwardStates = getForwardStates(actions);
		final List<ZoneState> backwardStates = getBakcwardStates(actions);

		for (int i = 0; i < forwardStates.size(); i++) {
			final ZoneState interpolant = ZoneState.interpolant(forwardStates.get(i), backwardStates.get(i));
			interpolants.add(interpolant);
		}

		return interpolants;
	}

	private List<ZoneState> getForwardStates(final List<? extends TCFAAction> actions) {
		final List<ZoneState> forwardStates = new ArrayList<>(actions.size() + 1);

		ZoneState lastState = ZoneState.top(precision.getClocks());
		forwardStates.add(lastState);

		for (final TCFAAction action : actions) {
			lastState = TCFAZoneTransferFunction.getInstance().post(lastState, action, precision);
			forwardStates.add(lastState);
		}

		assert forwardStates.size() == actions.size() + 1;

		return forwardStates;
	}

	private List<ZoneState> getBakcwardStates(final List<? extends TCFAAction> actions) {
		final List<ZoneState> backwardStates = new ArrayList<>(actions.size() + 1);

		ZoneState lastState = ZoneState.bottom(precision.getClocks());
		backwardStates.add(lastState);

		for (final TCFAAction action : actions) {
			lastState = TCFAZoneBackwardTransferFunction.getInstance().pre(lastState, action, precision);
			backwardStates.add(lastState);
		}

		assert backwardStates.size() == actions.size() + 1;

		return backwardStates;
	}

	@SuppressWarnings("unused")
	private static boolean isInterpolant(final List<? extends ZoneState> interpolant,
			final List<? extends TCFAAction> actions) {
		final Domain<ZoneState> domain = ZoneDomain.getInstance();
		final TransferFunction<ZoneState, TCFAAction, ZonePrecision> transferFunction = TCFAZoneTransferFunction
				.getInstance();

		if (interpolant.size() != actions.size() + 1) {
			return false;
		}

		final ZoneState first = interpolant.get(0);
		if (!domain.isTop(first)) {
			return false;
		}

		final ZoneState last = interpolant.get(interpolant.size() - 1);
		if (!domain.isBottom(last)) {
			return false;
		}

		for (int i = 0; i < actions.size(); i++) {

		}

		return true;
	}

}
