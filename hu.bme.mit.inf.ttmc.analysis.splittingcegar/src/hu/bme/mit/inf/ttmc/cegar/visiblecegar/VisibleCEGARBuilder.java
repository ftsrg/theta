package hu.bme.mit.inf.ttmc.cegar.visiblecegar;

import hu.bme.mit.inf.ttmc.cegar.common.GenericCEGARLoop;
import hu.bme.mit.inf.ttmc.cegar.common.ICEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.ILogger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.logging.NullLogger;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.IVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleChecker;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleConcretizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleInitializer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleRefiner;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement.InterpolatingVariableCollector;
import hu.bme.mit.inf.ttmc.constraint.z3.Z3ConstraintManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;

public class VisibleCEGARBuilder implements ICEGARBuilder {
	private STSManager manager = new STSManagerImpl(new Z3ConstraintManager());
	private ILogger logger = new NullLogger();
	private IVisualizer visualizer = new NullVisualizer();
	private boolean useCNFTransformation = false;

	@Override
	public VisibleCEGARBuilder manager(final STSManager manager) {
		this.manager = manager;
		return this;
	}

	/**
	 * Set logger
	 *
	 * @param logger
	 * @return Builder instance
	 */
	public VisibleCEGARBuilder logger(final ILogger logger) {
		this.logger = logger;
		return this;
	}

	/**
	 * Set visualizer
	 *
	 * @param visualizer
	 * @return Builder instance
	 */
	public VisibleCEGARBuilder visualizer(final IVisualizer visualizer) {
		this.visualizer = visualizer;
		return this;
	}

	/**
	 * Set whether CNF transformation should be applied to the constraints
	 *
	 * @param useCNFTransformation
	 *            True for CNF transformation, false otherwise
	 * @return Builder instance
	 */
	public VisibleCEGARBuilder useCNFTransformation(final boolean useCNFTransformation) {
		this.useCNFTransformation = useCNFTransformation;
		return this;
	}

	/**
	 * Build CEGAR loop instance
	 *
	 * @return CEGAR loop instance
	 */
	@Override
	public GenericCEGARLoop<VisibleAbstractSystem, VisibleAbstractState> build() {
		return new GenericCEGARLoop<>(new VisibleInitializer(manager, logger, visualizer, useCNFTransformation),
				new VisibleChecker(manager, logger, visualizer), new VisibleConcretizer(manager, logger, visualizer),
				new VisibleRefiner(manager, logger, visualizer, new InterpolatingVariableCollector(manager, logger, visualizer)), logger, "Visible");
	}
}
