package hu.bme.mit.theta.analysis.tcfa.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.Lists;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.zone.ZoneDomain;
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

		final List<ZoneState> forwardStates = getForwardStates(actions);
		final List<ZoneState> backwardStates = getBackwardStates(actions);

		for (int i = 0; i < forwardStates.size(); i++) {
			final ZoneState forwardState = forwardStates.get(i);
			final ZoneState backwardState = backwardStates.get(i);
			final ZoneState interpolant = ZoneState.interpolant(forwardState, backwardState);
			interpolants.add(interpolant);
		}

		return interpolants;
	}

	private List<ZoneState> getForwardStates(final List<? extends TcfaAction> actions) {
		final List<ZoneState> forwardStates = new ArrayList<>(actions.size() + 1);

		ZoneState lastState = ZoneState.top();
		forwardStates.add(lastState);

		for (final TcfaAction action : actions) {
			lastState = TcfaZoneTransferFunction.getInstance().post(lastState, action, precision);
			forwardStates.add(lastState);
		}

		// TODO
		assert forwardStates.get(forwardStates.size() - 1).isBottom();

		assert forwardStates.size() == actions.size() + 1;

		return forwardStates;
	}

	private List<ZoneState> getBackwardStates(final List<? extends TcfaAction> actions) {
		final List<ZoneState> backwardStates = new ArrayList<>(actions.size() + 1);

		ZoneState lastState = ZoneState.top();
		backwardStates.add(lastState);

		for (final TcfaAction action : Lists.reverse(actions)) {
			lastState = TcfaZoneBackwardTransferFunction.getInstance().pre(lastState, action, precision);
			backwardStates.add(0, lastState);
		}

		assert backwardStates.size() == actions.size() + 1;

		return backwardStates;
	}

	@SuppressWarnings("unused")
	private static boolean isInterpolant(final List<? extends ZoneState> interpolant,
			final List<? extends TcfaAction> actions) {
		final Domain<ZoneState> domain = ZoneDomain.getInstance();
		final TransferFunction<ZoneState, TcfaAction, ZonePrecision> transferFunction = TcfaZoneTransferFunction
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
