package hu.bme.mit.theta.analysis.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.formalism.sts.STS;

public final class StsLts implements LTS<State, StsAction> {

	final Collection<StsAction> actions;

	private StsLts(final STS sts) {
		checkNotNull(sts);
		this.actions = Collections.singleton(new StsAction(sts));
	}

	public static LTS<State, StsAction> create(final STS sts) {
		return new StsLts(sts);
	}

	@Override
	public Collection<StsAction> getEnabledActionsFor(final State state) {
		return actions;
	}

}
