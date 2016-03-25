package hu.bme.mit.inf.ttmc.cegar.visiblecegar;

import hu.bme.mit.inf.ttmc.cegar.common.GenericCEGARLoop;
import hu.bme.mit.inf.ttmc.cegar.common.ICEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleChecker;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleConcretizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleInitializer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.VisibleRefiner;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement.CraigItpVarCollector;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement.IVarCollector;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement.SeqItpVarCollector;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement.UnsatCoreVarCollector;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.utils.VisibleCEGARDebugger;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.common.logging.impl.NullLogger;

public class VisibleCEGARBuilder implements ICEGARBuilder {
	private Logger logger = new NullLogger();
	private Visualizer visualizer = new NullVisualizer();
	private boolean useCNFTransformation = false;
	private VariableCollectionMethod varCollMethod = VariableCollectionMethod.CraigItp;
	private VisibleCEGARDebugger debugger = null;

	public enum VariableCollectionMethod {
		CraigItp, SequenceItp, UnsatCore
	};

	/**
	 * Set logger
	 *
	 * @param logger
	 * @return Builder instance
	 */
	public VisibleCEGARBuilder logger(final Logger logger) {
		this.logger = logger;
		return this;
	}

	/**
	 * Set visualizer
	 *
	 * @param visualizer
	 * @return Builder instance
	 */
	public VisibleCEGARBuilder visualizer(final Visualizer visualizer) {
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

	public VisibleCEGARBuilder variableCollectionMethod(final VariableCollectionMethod method) {
		this.varCollMethod = method;
		return this;
	}

	public VisibleCEGARBuilder debug(final Visualizer visualizer) {
		if (visualizer == null)
			this.debugger = null;
		else
			this.debugger = new VisibleCEGARDebugger(visualizer);
		return this;
	}

	/**
	 * Build CEGAR loop instance
	 *
	 * @return CEGAR loop instance
	 */
	@Override
	public GenericCEGARLoop<VisibleAbstractSystem, VisibleAbstractState> build() {
		IVarCollector varCollector = null;
		switch (varCollMethod) {
		case CraigItp:
			varCollector = new CraigItpVarCollector(logger, visualizer);
			break;
		case SequenceItp:
			varCollector = new SeqItpVarCollector(logger, visualizer);
			break;
		case UnsatCore:
			varCollector = new UnsatCoreVarCollector(logger, visualizer);
			break;
		default:
			throw new RuntimeException("Unknown variable collection method: " + varCollMethod);
		}
		return new GenericCEGARLoop<>(new VisibleInitializer(logger, visualizer, useCNFTransformation), new VisibleChecker(logger, visualizer),
				new VisibleConcretizer(logger, visualizer), new VisibleRefiner(logger, visualizer, varCollector), debugger, logger, "Visible");
	}
}
