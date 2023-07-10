/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.xcfa.analysis.portfolio.common;

import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.validator.SolverValidatorWrapperFactory;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfig;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfigBuilder;
import hu.bme.mit.theta.xcfa.model.XCFA;

/**
 * This is a wrapper and extension to the {@link XcfaConfig} class It stores and is capable of
 * returning the information an {@link XcfaConfig} stores, but it also stores information on the
 * solvers used, if arg-cex check is used and if the solver is validated
 */
public class CegarConfiguration {

    public final XcfaConfigBuilder.Domain domain;
    public final XcfaConfigBuilder.Refinement refinement;
    public final XcfaConfigBuilder.Search search;
    public final XcfaConfigBuilder.PredSplit predSplit;
    public final XcfaConfigBuilder.Algorithm algorithm;
    public final int maxEnum;
    public final XcfaConfigBuilder.InitPrec initPrec;
    public final PruneStrategy pruneStrategy;
    public boolean argCexCheck;
    public final String abstractionSolver;
    public final String refinementSolver;
    public final boolean validateSolver;

    public CegarConfiguration(XcfaConfigBuilder.Domain domain,
        XcfaConfigBuilder.Refinement refinement,
        XcfaConfigBuilder.Search search,
        XcfaConfigBuilder.PredSplit predSplit,
        XcfaConfigBuilder.Algorithm algorithm,
        int maxEnum,
        XcfaConfigBuilder.InitPrec initPrec,
        PruneStrategy pruneStrategy,
        boolean argCexCheck,
        String abstractionSolver,
        String refinementSolver,
        boolean validateSolver) {
        this.domain = domain;
        this.refinement = refinement;
        this.search = search;
        this.predSplit = predSplit;
        this.algorithm = algorithm;
        this.maxEnum = maxEnum;
        this.initPrec = initPrec;
        this.pruneStrategy = pruneStrategy;
        this.argCexCheck = argCexCheck;
        this.abstractionSolver = abstractionSolver;
        this.refinementSolver = refinementSolver;
        this.validateSolver = validateSolver;
    }

    public CegarConfiguration(XcfaConfigBuilder.Domain domain,
        XcfaConfigBuilder.Refinement refinement,
        XcfaConfigBuilder.Search search,
        XcfaConfigBuilder.PredSplit predSplit,
        XcfaConfigBuilder.Algorithm algorithm,
        int maxEnum,
        XcfaConfigBuilder.InitPrec initPrec,
        PruneStrategy pruneStrategy,
        boolean argCexCheck,
        String abstractionSolver,
        String refinementSolver) {
        this.domain = domain;
        this.refinement = refinement;
        this.search = search;
        this.predSplit = predSplit;
        this.algorithm = algorithm;
        this.maxEnum = maxEnum;
        this.initPrec = initPrec;
        this.pruneStrategy = pruneStrategy;
        this.argCexCheck = argCexCheck;
        this.abstractionSolver = abstractionSolver;
        this.refinementSolver = refinementSolver;
        this.validateSolver = false;
    }

    /**
     * Sets up arg-cex check (if it is enabled) and builds configuration
     */
    public XcfaConfig<?, ?, ?> buildConfiguration(XCFA xcfa, ConsoleLogger logger)
        throws Exception {
        // set up Arg-Cex check
        if (!argCexCheck) {
            ArgCexCheckHandler.instance.setArgCexCheck(false, false);
        } else {
            ArgCexCheckHandler.instance.setArgCexCheck(true,
                refinement.equals(XcfaConfigBuilder.Refinement.MULTI_SEQ));
        }

        try {
            SolverFactory refinementSolverFactory;
            SolverFactory abstractionSolverFactory;
            if (validateSolver) {
                refinementSolverFactory = SolverValidatorWrapperFactory.create(refinementSolver);
                abstractionSolverFactory = SolverValidatorWrapperFactory.create(abstractionSolver);
            } else {
                refinementSolverFactory = SolverManager.resolveSolverFactory(refinementSolver);
                abstractionSolverFactory = SolverManager.resolveSolverFactory(abstractionSolver);
            }
            return new XcfaConfigBuilder(domain, refinement, refinementSolverFactory,
                abstractionSolverFactory, algorithm)
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
            ", abstraction solver=" + abstractionSolver +
            ", refinement solver=" + refinementSolver +
            '}';
    }

}
