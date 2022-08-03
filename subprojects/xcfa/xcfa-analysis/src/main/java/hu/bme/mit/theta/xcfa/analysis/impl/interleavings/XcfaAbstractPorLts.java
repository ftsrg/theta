package hu.bme.mit.theta.xcfa.analysis.impl.interleavings;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.util.Collection;

public class XcfaAbstractPorLts extends XcfaPorLts {

	private Prec precision;

	public XcfaAbstractPorLts(XCFA xcfa) {
		super(xcfa);
	}

	@Override
	public <P extends Prec> Collection<XcfaAction> getEnabledActionsFor(XcfaState<?> state, P prec) {
		precision = prec;
		var result = getEnabledActionsFor(state);
		if (true || prec.getUsedVars().stream().anyMatch(v -> "x".equals(v.getName()))) {
			if (state.getEnabledProcesses().stream().map(p -> state.getProcessLocs().get(p)).anyMatch(loc -> "tmp463".equals(loc.getName()))) {
				var pr = state.getEnabledProcesses().stream().filter(p -> state.getProcessLocs().get(p).getName().equals("tmp463")).findFirst();
				if (pr.isPresent() && result.stream().anyMatch(a -> a.getProcess().equals(pr.get()))) {
					int a = 2;
				}
			}
		}
		return result;
	}

	private boolean isIgnorable(Decl<? extends Type> varDecl) {
		Collection<? extends Decl<? extends Type>> usedVars = precision.getUsedVars();
		return !usedVars.contains(varDecl);
	}

	@Override
	protected boolean areDependents(XcfaAction persistentSetAction, XcfaAction action) {
		return canEnOrDisableEachOther(persistentSetAction, action) ||
				getInfluencedSharedObjects(getTransitionOf(action)).stream().anyMatch(varDecl -> {
					if (isIgnorable(varDecl)) return false;
					return getCachedUsedSharedObjects(getTransitionOf(persistentSetAction)).contains(varDecl);
				});
	}
}
