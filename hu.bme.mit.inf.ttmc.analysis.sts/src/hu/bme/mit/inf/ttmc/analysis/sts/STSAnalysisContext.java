package hu.bme.mit.inf.ttmc.analysis.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.analysis.AnalysisContext;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

public class STSAnalysisContext implements AnalysisContext<State, STSAction> {

	final Collection<STSAction> actions;

	public STSAnalysisContext(final STS sts) {
		checkNotNull(sts);
		this.actions = Collections.singleton(new STSAction(sts));
	}

	@Override
	public Collection<? extends STSAction> getEnabledActionsFor(final State state) {
		return actions;
	}

}
