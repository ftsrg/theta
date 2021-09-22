package hu.bme.mit.theta.xcfa.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfig;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

class CegarConfiguration {
	public final CfaConfigBuilder.Domain domain;
	public final CfaConfigBuilder.Refinement refinement;
	public final CfaConfigBuilder.PrecGranularity precGranularity;
	public final CfaConfigBuilder.Search search;
	public final CfaConfigBuilder.PredSplit predSplit;
	public final int maxEnum;
	public final CfaConfigBuilder.InitPrec initPrec;
	public final PruneStrategy pruneStrategy;
	public CfaConfigBuilder.Encoding encoding;
	public boolean argCexCheck;

	CegarConfiguration(CfaConfigBuilder.Domain domain,
				  CfaConfigBuilder.Refinement refinement,
				  CfaConfigBuilder.PrecGranularity precGranularity,
				  CfaConfigBuilder.Search search,
				  CfaConfigBuilder.PredSplit predSplit,
				  int maxEnum,
				  CfaConfigBuilder.InitPrec initPrec,
				  PruneStrategy pruneStrategy,
				  CfaConfigBuilder.Encoding encoding,
				  boolean argCexCheck) {
		this.domain = domain;
		this.refinement = refinement;
		this.precGranularity = precGranularity;
		this.search = search;
		this.predSplit = predSplit;
		this.maxEnum = maxEnum;
		this.initPrec = initPrec;
		this.pruneStrategy = pruneStrategy;
		this.encoding = encoding;
		this.argCexCheck = argCexCheck;
	}

	/** sets up arg cex check and builds configuration */
	public CfaConfig<?, ?, ?> buildConfiguration(CFA cfa, CFA.Loc errLoc, ConsoleLogger logger) throws Exception {
		// set up Arg-Cex check
		if(!argCexCheck) {
			ArgCexCheckHandler.instance.setArgCexCheck(false, false);
		} else {
			if(refinement.equals(CfaConfigBuilder.Refinement.MULTI_SEQ)) {
				ArgCexCheckHandler.instance.setArgCexCheck(true, true);
			} else {
				ArgCexCheckHandler.instance.setArgCexCheck(true, false);
			}
		}

		try {
			return new CfaConfigBuilder(domain, refinement, Z3SolverFactory.getInstance())
					.precGranularity(precGranularity).search(search)
					.predSplit(predSplit).encoding(CfaConfigBuilder.Encoding.LBE).maxEnum(maxEnum).initPrec(initPrec)
					.pruneStrategy(pruneStrategy).logger(logger).build(cfa, errLoc);

		} catch (final Exception ex) {
			throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
		}
	}

	@Override
	public String toString() {
		return "Configuration{" +
				"domain=" + domain +
				", refinement=" + refinement +
				", precGranularity=" + precGranularity +
				", search=" + search +
				", predSplit=" + predSplit +
				", maxEnum=" + maxEnum +
				", initPrec=" + initPrec +
				", pruneStrategy=" + pruneStrategy +
				", argCexCheck=" + argCexCheck +
				'}';
	}

}
