package hu.bme.mit.inf.ttmc.system.ui;

import hu.bme.mit.inf.ttmc.program.sts.STS;

/**
 * Symbolic Transition System model interface.
 * @author Akos
 */
public interface STSModel {
	/**
	 * Get the converted Symbolic Transition System.
	 * @return Symbolic Transition System
	 */
	public STS getSTS();
}
