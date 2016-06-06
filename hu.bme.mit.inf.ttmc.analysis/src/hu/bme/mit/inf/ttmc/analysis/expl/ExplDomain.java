package hu.bme.mit.inf.ttmc.analysis.expl;

import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class ExplDomain implements Domain<ExplState> {

	private static final ExplDomain INSTANCE;

	static {
		INSTANCE = new ExplDomain();
	}

	private ExplDomain() {

	}

	public static ExplDomain create() {
		return INSTANCE;
	}

	@Override
	public boolean isTop(final ExplState state) {
		return state.getVars().isEmpty();
	}

	@Override
	public boolean isBottom(final ExplState state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isLeq(final ExplState state1, final ExplState state2) {
		for (final VarDecl<? extends Type> varDecl : state2.getVars()) {
			if (!state1.getVars().contains(varDecl) || !state2.getValue(varDecl).equals(state1.getValue(varDecl)))
				return false;
		}
		return true;
	}

	@Override
	public ExplState join(final ExplState state1, final ExplState state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

}
