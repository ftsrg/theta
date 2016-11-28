package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public final class ExplDomain implements Domain<ExplState> {

	private static final ExplDomain INSTANCE;

	static {
		INSTANCE = new ExplDomain();
	}

	private ExplDomain() {
	}

	public static ExplDomain getInstance() {
		return INSTANCE;
	}

	@Override
	public boolean isTop(final ExplState state) {
		return state.getDecls().isEmpty();
	}

	@Override
	public boolean isBottom(final ExplState state) {
		return false;
	}

	@Override
	public boolean isLeq(final ExplState state1, final ExplState state2) {
		for (final VarDecl<? extends Type> varDecl : state2.getDecls()) {
			if (!state1.getDecls().contains(varDecl) || !state2.getValue(varDecl).equals(state1.getValue(varDecl))) {
				return false;
			}
		}
		return true;
	}

}
