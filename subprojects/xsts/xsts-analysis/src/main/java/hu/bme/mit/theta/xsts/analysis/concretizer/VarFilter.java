package hu.bme.mit.theta.xsts.analysis.concretizer;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Optional;

public final class VarFilter {

	private final XSTS xsts;

	private VarFilter(final XSTS xsts) {
		this.xsts = xsts;
	}

	public static VarFilter of(final XSTS xsts) {
		return new VarFilter(xsts);
	}

	public Valuation filter(final Valuation valuation) {
		MutableValuation filteredValuation = new MutableValuation();
		for (VarDecl decl : xsts.getVars()) {
			Optional<LitExpr> val = valuation.eval(decl);
			if (val.isPresent()) filteredValuation.put(decl, val.get());
		}
		return filteredValuation;
	}

}
