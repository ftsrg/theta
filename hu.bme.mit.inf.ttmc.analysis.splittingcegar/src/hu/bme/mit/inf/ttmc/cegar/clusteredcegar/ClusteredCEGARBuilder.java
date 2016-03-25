package hu.bme.mit.inf.ttmc.cegar.clusteredcegar;

import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractState;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps.ClusteredChecker;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps.ClusteredConcretizer;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps.ClusteredInitializer;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.steps.ClusteredRefiner;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.utils.ClusteredCEGARDebugger;
import hu.bme.mit.inf.ttmc.cegar.common.CEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.common.GenericCEGARLoop;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.NullVisualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.common.logging.impl.NullLogger;

public class ClusteredCEGARBuilder implements CEGARBuilder {
	private Logger logger = new NullLogger();
	private Visualizer visualizer = new NullVisualizer();
	private ClusteredCEGARDebugger debugger = null;

	public ClusteredCEGARBuilder logger(final Logger logger) {
		this.logger = logger;
		return this;
	}

	public ClusteredCEGARBuilder visualizer(final Visualizer visualizer) {
		this.visualizer = visualizer;
		return this;
	}

	public ClusteredCEGARBuilder debug(final Visualizer visualizer) {
		if (visualizer == null)
			debugger = null;
		else
			debugger = new ClusteredCEGARDebugger(visualizer);
		return this;
	}

	@Override
	public GenericCEGARLoop<ClusteredAbstractSystem, ClusteredAbstractState> build() {
		return new GenericCEGARLoop<ClusteredAbstractSystem, ClusteredAbstractState>(new ClusteredInitializer(logger, visualizer),
				new ClusteredChecker(logger, visualizer), new ClusteredConcretizer(logger, visualizer), new ClusteredRefiner(logger, visualizer), debugger,
				logger, "Clustered");
	}
}
