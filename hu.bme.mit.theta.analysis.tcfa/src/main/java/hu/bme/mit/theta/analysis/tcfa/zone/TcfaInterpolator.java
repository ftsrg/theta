package hu.bme.mit.theta.analysis.tcfa.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.Lists;

import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaZoneUtils;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public final class TcfaInterpolator {

	private final ZonePrecision precision;

	private TcfaInterpolator(final ZonePrecision precision) {
		this.precision = checkNotNull(precision);
	}

	public static TcfaInterpolator create(final ZonePrecision precision) {
		return new TcfaInterpolator(precision);
	}

	public List<ZoneState> getInterpolant(final List<? extends TcfaAction> actions) {
		final List<ZoneState> interpolants = new ArrayList<>(actions.size() + 1);
		final List<ZoneState> backwardStates = getBackwardStates(actions);
		interpolants.add(ZoneState.top());
		for (int i = 0; i < actions.size() - 1; i++) {
			final TcfaAction action = actions.get(i);
			final ZoneState prevItp = interpolants.get(i);
			final ZoneState forwardState = TcfaZoneUtils.post(prevItp, action, precision);
			final ZoneState backwardState = backwardStates.get(i + 1);
			final ZoneState interpolant = ZoneState.interpolant(forwardState, backwardState);
			interpolants.add(interpolant);
		}
		interpolants.add(ZoneState.bottom());
		return interpolants;
	}

	private List<ZoneState> getBackwardStates(final List<? extends TcfaAction> actions) {
		final List<ZoneState> backwardStates = new ArrayList<>(actions.size() + 1);

		ZoneState lastState = ZoneState.top();
		backwardStates.add(lastState);

		for (final TcfaAction action : Lists.reverse(actions)) {
			lastState = TcfaZoneUtils.pre(lastState, action, precision);
			backwardStates.add(0, lastState);
		}

		assert backwardStates.size() == actions.size() + 1;

		return backwardStates;
	}

}
