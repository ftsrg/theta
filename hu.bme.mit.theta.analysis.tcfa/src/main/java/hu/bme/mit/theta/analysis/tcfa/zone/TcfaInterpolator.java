package hu.bme.mit.theta.analysis.tcfa.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.Lists;

import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaZoneUtils;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public final class TcfaInterpolator {

	private final ZonePrec prec;

	private TcfaInterpolator(final ZonePrec prec) {
		this.prec = checkNotNull(prec);
	}

	public static TcfaInterpolator create(final ZonePrec prec) {
		return new TcfaInterpolator(prec);
	}

	public List<ZoneState> getInterpolant(final ZoneState source, final List<? extends TcfaAction> actions,
			final ZoneState target) {

		final List<ZoneState> backwardStates = getBackwardStates(target, actions);
		final List<ZoneState> interpolants = new ArrayList<>(actions.size() + 1);

		ZoneState A = source;
		ZoneState B = backwardStates.get(0);
		ZoneState I = ZoneState.interpolant(A, B);
		interpolants.add(I);

		for (int i = 0; i < actions.size(); i++) {
			final TcfaAction action = actions.get(i);
			A = TcfaZoneUtils.post(I, action, prec);
			B = backwardStates.get(i + 1);
			I = ZoneState.interpolant(A, B);
			interpolants.add(I);
		}

		return interpolants;
	}

	public List<ZoneState> getInterpolant(final List<? extends TcfaAction> actions) {
		return getInterpolant(ZoneState.top(), actions, ZoneState.top());
	}

	private List<ZoneState> getBackwardStates(final ZoneState state, final List<? extends TcfaAction> actions) {
		final List<ZoneState> backwardStates = new ArrayList<>(actions.size() + 1);

		ZoneState lastState = state;
		backwardStates.add(lastState);

		for (final TcfaAction action : Lists.reverse(actions)) {
			lastState = TcfaZoneUtils.pre(lastState, action, prec);
			backwardStates.add(0, lastState);
		}

		assert backwardStates.size() == actions.size() + 1;

		return backwardStates;
	}

}
