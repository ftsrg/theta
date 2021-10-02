package hu.bme.mit.theta.xcfa.analysis.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfig;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfigBuilder;
import hu.bme.mit.theta.xcfa.model.XCFA;

class CegarConfiguration {
	public final XcfaConfigBuilder.Domain domain;
	public final XcfaConfigBuilder.Refinement refinement;
	public final XcfaConfigBuilder.Search search;
	public final XcfaConfigBuilder.PredSplit predSplit;
	public final XcfaConfigBuilder.Algorithm algorithm;
	public final int maxEnum;
	public final XcfaConfigBuilder.InitPrec initPrec;
	public final PruneStrategy pruneStrategy;
	public boolean argCexCheck;

	CegarConfiguration(XcfaConfigBuilder.Domain domain,
				  XcfaConfigBuilder.Refinement refinement,
				  XcfaConfigBuilder.Search search,
				  XcfaConfigBuilder.PredSplit predSplit,
				  XcfaConfigBuilder.Algorithm algorithm,
				  int maxEnum,
				  XcfaConfigBuilder.InitPrec initPrec,
				  PruneStrategy pruneStrategy,
				  boolean argCexCheck) {
		this.domain = domain;
		this.refinement = refinement;
		this.search = search;
		this.predSplit = predSplit;
		this.algorithm = algorithm;
		this.maxEnum = maxEnum;
		this.initPrec = initPrec;
		this.pruneStrategy = pruneStrategy;
		this.argCexCheck = argCexCheck;
	}

	/** sets up arg cex check and builds configuration */
	public XcfaConfig<?, ?, ?> buildConfiguration(XCFA xcfa, ConsoleLogger logger) throws Exception {
		// set up Arg-Cex check
		if(!argCexCheck) {
			ArgCexCheckHandler.instance.setArgCexCheck(false, false);
		} else {
			ArgCexCheckHandler.instance.setArgCexCheck(true, refinement.equals(XcfaConfigBuilder.Refinement.MULTI_SEQ));
		}

		try {
			return new XcfaConfigBuilder(domain, refinement, Z3SolverFactory.getInstance(), algorithm)
					.search(search)
					.predSplit(predSplit).maxEnum(maxEnum).initPrec(initPrec)
					.pruneStrategy(pruneStrategy).logger(logger).build(xcfa);

		} catch (final Exception ex) {
			throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
		}
	}

	@Override
	public String toString() {
		return "Configuration{" +
				"domain=" + domain +
				", refinement=" + refinement +
				", search=" + search +
				", predSplit=" + predSplit +
				", algorithm=" + algorithm +
				", maxEnum=" + maxEnum +
				", initPrec=" + initPrec +
				", pruneStrategy=" + pruneStrategy +
				", argCexCheck=" + argCexCheck +
				'}';
	}

}
