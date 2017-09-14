/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.tools;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.StsUtils;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.StsSpec;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.tools.sts.StsConfigBuilder;
import hu.bme.mit.theta.tools.sts.StsConfigBuilder.Domain;
import hu.bme.mit.theta.tools.sts.StsConfigBuilder.InitPrec;
import hu.bme.mit.theta.tools.sts.StsConfigBuilder.PredSplit;
import hu.bme.mit.theta.tools.sts.StsConfigBuilder.Refinement;
import hu.bme.mit.theta.tools.sts.StsConfigBuilder.Search;

public class SandBox {
	public static void main(final String[] args) throws FileNotFoundException, IOException {
		final StsSpec spec = StsDslManager
				.createStsSpec(new FileInputStream("src/test/resources/simple/simple2.system"));
		STS sts = spec.getAllSts().iterator().next();
		sts = StsUtils.eliminateIte(sts);

		System.out.println("Press a key to start");
		System.in.read();

		//		final STS sts = new AigerParserSimple().parse("src/test/resources/hw/srg5ptimo.aag");

		System.out.println(sts);

		final Logger logger = new ConsoleLogger(100);

		final Config<? extends State, ? extends Action, ? extends Prec> configuration = new StsConfigBuilder(
				Domain.PRED, Refinement.BW_BIN_ITP).initPrec(InitPrec.EMPTY).search(Search.BFS)
						.predSplit(PredSplit.WHOLE).logger(logger).solverFactory(Z3SolverFactory.getInstace())
						.build(sts);

		configuration.check();
	}
}
