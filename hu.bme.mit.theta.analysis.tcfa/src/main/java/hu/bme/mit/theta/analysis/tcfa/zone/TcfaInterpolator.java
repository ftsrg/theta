package hu.bme.mit.theta.analysis.tcfa.zone;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.analysis.expr.ExprStateUtils.anyUncoveredSuccessor;
import static java.util.Collections.singleton;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import com.google.common.collect.Lists;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaZoneUtils;
import hu.bme.mit.theta.analysis.zone.ZoneDomain;
import hu.bme.mit.theta.analysis.zone.ZonePrecision;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

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
		// final List<ZoneState> forwardStates = getForwardStates(actions);
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

		assert isInterpolant(interpolants, actions);
		return interpolants;
	}

	@SuppressWarnings("unused")
	private List<ZoneState> getForwardStates(final List<? extends TcfaAction> actions) {
		final List<ZoneState> forwardStates = new ArrayList<>(actions.size() + 1);

		ZoneState lastState = ZoneState.top();
		forwardStates.add(lastState);

		for (final TcfaAction action : actions) {
			lastState = TcfaZoneUtils.post(lastState, action, precision);
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
			lastState = TcfaZoneUtils.pre(lastState, action, precision);
			backwardStates.add(0, lastState);
		}

		assert backwardStates.size() == actions.size() + 1;

		return backwardStates;
	}

	private static boolean isInterpolant(final List<? extends ZoneState> interpolant,
			final List<? extends TcfaAction> actions) {
		final Domain<ZoneState> domain = ZoneDomain.getInstance();

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

		final Solver solver = Z3SolverFactory.getInstace().createSolver();
		for (int i = 0; i < actions.size(); i++) {
			final ZoneState state = interpolant.get(i);
			final TcfaAction action = actions.get(i);
			final ZoneState succState = interpolant.get(i + 1);

			final Optional<Valuation> uncoveredSuccessor = anyUncoveredSuccessor(state, action, singleton(succState),
					solver);
			if (uncoveredSuccessor.isPresent()) {
				return false;
			}
		}

		return true;
	}

}
