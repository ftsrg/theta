package hu.bme.mit.theta.analysis.zone.lu;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.expr.ExprDomain;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

final class LuZoneDomain implements Domain<LuZoneState> {
	private static final LuZoneDomain INSTANCE = new LuZoneDomain();

	private final ExprDomain domain;

	private LuZoneDomain() {
		domain = ExprDomain.create(Z3SolverFactory.getInstace().createSolver());
	}

	public static LuZoneDomain getInstance() {
		return INSTANCE;
	}

	@Override
	public boolean isTop(final LuZoneState state) {
		return domain.isTop(state);
	}

	@Override
	public boolean isBottom(final LuZoneState state) {
		return state.isBottom();
	}

	@Override
	public boolean isLeq(final LuZoneState state1, final LuZoneState state2) {
		return domain.isLeq(state1, state2);
	}

}
