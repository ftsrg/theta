package hu.bme.mit.inf.theta.system.ui;

import java.util.Collection;

import hu.bme.mit.inf.theta.formalism.sts.STS;

/**
 * System model interface. Contains a collection of Symbolic
 * Transition Systems.
 * @author Akos
 */
public interface SystemModel {
	/**
	 * Get the collection of Symbolic Transition Systems.
	 * @return Collection of Symbolic Transition Systems
	 */
	public Collection<STS> getSTSs();
	
}
