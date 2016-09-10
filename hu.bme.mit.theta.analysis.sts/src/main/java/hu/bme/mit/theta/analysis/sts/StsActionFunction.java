package hu.bme.mit.theta.analysis.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.ActionFunction;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.formalism.sts.STS;

public class StsActionFunction implements ActionFunction<State, StsAction> {

	final Collection<StsAction> actions;

	public StsActionFunction(final STS sts) {
		checkNotNull(sts);
		this.actions = Collections.singleton(new StsAction(sts));
	}

	@Override
	public Collection<? extends StsAction> getEnabledActionsFor(final State state) {
		return actions;
	}

}
