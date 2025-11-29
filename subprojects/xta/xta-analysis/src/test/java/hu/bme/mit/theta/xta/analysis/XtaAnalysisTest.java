/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicArgAbstractor;
import hu.bme.mit.theta.analysis.unit.UnitAnalysis;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.unit.UnitState;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public final class XtaAnalysisTest {

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"/critical-2-25-50.xta"},
                    {"/csma-2.xta"},
                    {"/fddi-2.xta"},
                    {"/fischer-2-32-64.xta"},
                    {"/lynch-2-16.xta"},
                    {"/broadcast.xta"},
                });
    }
    public String filepath;

    @MethodSource("data")
    @ParameterizedTest(name = "{0}")
    public void test(String filepath) throws FileNotFoundException, IOException {
        initXtaAnalysisTest(filepath);
        final InputStream inputStream = getClass().getResourceAsStream(filepath);
        final XtaSystem system = XtaDslManager.createSystem(inputStream);

        final LTS<XtaState<?>, XtaAction> lts = XtaLts.create(system);
        final Analysis<XtaState<UnitState>, XtaAction, UnitPrec> analysis =
                XtaAnalysis.create(system, UnitAnalysis.getInstance());
        final ArgBuilder<XtaState<UnitState>, XtaAction, UnitPrec> argBuilder =
                ArgBuilder.create(lts, analysis, s -> false);

        final ArgAbstractor<XtaState<UnitState>, XtaAction, UnitPrec> abstractor =
                BasicArgAbstractor.builder(argBuilder).projection(s -> s.getLocs()).build();

        final ARG<XtaState<UnitState>, XtaAction> arg = abstractor.createProof();
        abstractor.check(arg, UnitPrec.getInstance());

        System.out.println(
                GraphvizWriter.getInstance()
                        .writeString(ArgVisualizer.getDefault().visualize(arg)));
    }

    public void initXtaAnalysisTest(String filepath) {
        this.filepath = filepath;
    }
}
