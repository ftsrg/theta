package hu.bme.mit.inf.ttmc.system.ui;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.program.sts.STS;

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
