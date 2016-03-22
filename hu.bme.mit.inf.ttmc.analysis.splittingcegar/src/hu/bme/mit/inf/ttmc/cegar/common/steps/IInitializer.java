package hu.bme.mit.inf.ttmc.cegar.common.steps;

import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractSystem;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Common interface for creating the initial abstract system.
 *
 * @author Akos
 * @param <AbstractSystemType>
 *            Type of the abstract system
 */
public interface IInitializer<AbstractSystemType extends IAbstractSystem> extends IStoppable {
	/**
	 * Create the initial abstraction
	 *
	 * @param sts
	 *            Concrete system
	 * @return Initial abstract system
	 */
	AbstractSystemType create(STS concrSys);
}
