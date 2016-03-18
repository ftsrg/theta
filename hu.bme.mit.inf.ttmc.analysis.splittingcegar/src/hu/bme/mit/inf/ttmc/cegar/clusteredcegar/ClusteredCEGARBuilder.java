package hu.bme.mit.inf.ttmc.cegar.clusteredcegar;

import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractState;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps.ClusteredChecker;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps.ClusteredConcretizer;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps.ClusteredInitializer;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps.ClusteredRefiner;
import hu.bme.mit.inf.ttmc.cegar.common.GenericCEGARLoop;
import hu.bme.mit.inf.ttmc.cegar.common.ICEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.ILogger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.NullLogger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.inf.ttmc.constraint.z3.Z3ConstraintManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;

public class ClusteredCEGARBuilder implements ICEGARBuilder {
	private STSManager manager = new STSManagerImpl(new Z3ConstraintManager());
	private ILogger logger = new NullLogger();
	private IVisualizer visualizer = new NullVisualizer();

	@Override
	public ClusteredCEGARBuilder manager(final STSManager manager) {
		this.manager = manager;
		return this;
	}

	/**
	 * Set logger
	 *
	 * @param logger
	 * @return Builder instance
	 */
	public ClusteredCEGARBuilder logger(final ILogger logger) {
		this.logger = logger;
		return this;
	}

	/**
	 * Set visualizer
	 *
	 * @param visualizer
	 * @return Builder instance
	 */
	public ClusteredCEGARBuilder visualizer(final IVisualizer visualizer) {
		this.visualizer = visualizer;
		return this;
	}

	/**
	 * Build CEGAR loop instance
	 *
	 * @return CEGAR loop instance
	 */
	@Override
	public GenericCEGARLoop<ClusteredAbstractSystem, ClusteredAbstractState> build() {
		return new GenericCEGARLoop<ClusteredAbstractSystem, ClusteredAbstractState>(new ClusteredInitializer(manager, logger, visualizer),
				new ClusteredChecker(manager, logger, visualizer), new ClusteredConcretizer(manager, logger, visualizer),
				new ClusteredRefiner(manager, logger, visualizer), logger, "Clustered");
	}
}
