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
package hu.bme.mit.theta.xta.analysis;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;
import java.util.stream.Collectors;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;

@RunWith(Parameterized.class)
public final class XtaZoneAnalysisTest {

	@Parameters(name = "{0}")
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{"/csma-2.xta"},

				{"/fddi-2.xta"},

				{"/fischer-2-32-64.xta"},

				{"/lynch-2-16.xta"},

				{"/broadcast.xta"},

		});
	}

	@Parameter(0)
	public String filepath;

	@Test
	public void test() throws FileNotFoundException, IOException {
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		final XtaSystem system = XtaDslManager.createSystem(inputStream);

		final LTS<XtaState<?>, XtaAction> lts = XtaLts.create(system);
		final Analysis<ExplState, XtaAction, UnitPrec> explAnalysis = XtaExplAnalysis.create(system);
		final Analysis<ZoneState, XtaAction, ZonePrec> zoneAnalysis = XtaZoneAnalysis.getInstance();
		final Analysis<Prod2State<ExplState, ZoneState>, XtaAction, Prod2Prec<UnitPrec, ZonePrec>> prodAnalysis = Prod2Analysis
				.create(explAnalysis, zoneAnalysis);
		final Analysis<Prod2State<ExplState, ZoneState>, XtaAction, ZonePrec> mappedAnalysis = PrecMappingAnalysis
				.create(prodAnalysis, z -> Prod2Prec.of(UnitPrec.getInstance(), z));
		final Analysis<XtaState<Prod2State<ExplState, ZoneState>>, XtaAction, ZonePrec> analysis = XtaAnalysis
				.create(system, mappedAnalysis);

		final ZonePrec prec = ZonePrec.of(system.getClockVars());

		final ArgBuilder<XtaState<Prod2State<ExplState, ZoneState>>, XtaAction, ZonePrec> argBuilder = ArgBuilder
				.create(lts, analysis, s -> false);

		final Abstractor<XtaState<Prod2State<ExplState, ZoneState>>, XtaAction, ZonePrec> abstractor = BasicAbstractor
				.builder(argBuilder).projection(s -> s.getLocs()).build();

		final ARG<XtaState<Prod2State<ExplState, ZoneState>>, XtaAction> arg = abstractor.createArg();
		abstractor.check(arg, prec);

		System.out.println(arg.getNodes().collect(Collectors.toSet()));

		System.out.println(arg.getNodes().count());
	}

}
