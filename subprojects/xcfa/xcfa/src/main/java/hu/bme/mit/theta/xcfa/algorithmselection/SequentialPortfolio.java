package hu.bme.mit.theta.xcfa.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;

import java.io.File;
import java.lang.module.Configuration;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;

// TODO logging
// TODO remove arg/cex check
public class SequentialPortfolio extends AbstractPortfolio {
	CegarConfiguration[] configurations = new CegarConfiguration[3];

	public SequentialPortfolio(Logger.Level logLevel, File statistics) {
		super(logLevel, statistics);
		configurations[0] = new CegarConfiguration(
				CfaConfigBuilder.Domain.EXPL,
				CfaConfigBuilder.Refinement.SEQ_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE
		);
		configurations[1] = new CegarConfiguration(
				CfaConfigBuilder.Domain.PRED_CART,
				CfaConfigBuilder.Refinement.BW_BIN_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE
		);
		configurations[2] = new CegarConfiguration(
				CfaConfigBuilder.Domain.EXPL,
				CfaConfigBuilder.Refinement.NWT_IT_WP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE
		);
	}

	@Override
	public SafetyResult<?, ?> executeAnalysis(CFA cfa) {
		for (CegarConfiguration configuration : configurations) {
			System.out.println("Executing configuration: " + configuration);

			// TODO set timeout to remaining of 900 (max 300) - cfa creation
			Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, cfa, 5);
			if(result.get1().equals(Result.SUCCESS)) {
				checkState(result.get2().isPresent());
				return result.get2().get();
			}
		}
		return null;
	}
}
