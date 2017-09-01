package hu.bme.mit.theta.formalism.sts.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.formalism.sts.STS;

/**
 * An LTS implementation for the STS formalism. The STS has only one enabled
 * Action for every State, namely the transition relation.
 */
public final class StsLts implements LTS<State, StsAction> {

	private final Collection<StsAction> actions;

	private StsLts(final STS sts) {
		checkNotNull(sts);
		this.actions = Collections.singleton(new StsAction(sts));
	}

	/**
	 * Creates a new LTS based on a STS.
	 *
	 * @param sts
	 * @return
	 */
	public static LTS<State, StsAction> create(final STS sts) {
		return new StsLts(sts);
	}

	@Override
	public Collection<StsAction> getEnabledActionsFor(final State state) {
		return actions;
	}

}
