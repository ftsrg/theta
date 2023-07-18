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

package hu.bme.mit.theta.fronted.litmus2xcfa;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.frontend.litmus2xcfa.LitmusInterpreter;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import kotlin.Pair;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

@RunWith(Parameterized.class)
public class LitmusTest {
    @Parameterized.Parameter(0)
    public String filepath;

    @Parameterized.Parameter(1)
    public int globalsNum;

    @Parameterized.Parameter(2)
    public int threadNum;

    @Parameterized.Parameter(3)
    public List<Integer> instructionPerThread;

    @Parameterized.Parameter(4)
    public String mcmFilename;


    @Parameterized.Parameters
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{
                {"/LB.litmus", 2, 2, List.of(11, 7), "/aarch64.cat"},
        });
    }

    @Test
    public void parse() throws IOException {
        final XCFA xcfa = LitmusInterpreter.getXcfa(getClass().getResourceAsStream(filepath));

        Assert.assertEquals(globalsNum, xcfa.getVars().size());
        Assert.assertEquals(threadNum, xcfa.getInitProcedures().size());
        final List<Pair<XcfaProcedure, List<Expr<?>>>> processes = xcfa.getInitProcedures();
        for (int i = 0; i < processes.size(); i++) {
            XcfaProcedure procedure = processes.get(i).getFirst();
            Assert.assertEquals((int) instructionPerThread.get(i), procedure.getEdges().size());
        }
    }

    @Test
    public void check() throws IOException {
        try (Solver solver = Z3SolverFactory.getInstance().createSolver()) {
            final XCFA xcfa = LitmusInterpreter.getXcfa(getClass().getResourceAsStream(filepath));
            final List<Pair<XcfaProcedure, List<Expr<?>>>> processes = xcfa.getInitProcedures();
            final List<Integer> processIds = new ArrayList<>();
            for (int i = 0; i < processes.size(); i++) {
                processIds.add(i * -1 - 1);
            }
        } catch (Exception e) {
            throw new RuntimeException(e);
        }

//        final XcfaProcessMemEventProvider<ExplState> memEventProvider = new XcfaProcessMemEventProvider<>(processes.size());
//        final MultiprocLTS<XcfaProcessState<ExplState>, XcfaProcessAction> multiprocLTS = new MultiprocLTS<>(processIds.stream().map(id -> Map.entry(id, new XcfaProcessLTS<ExplState>())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
//        final MultiprocInitFunc<XcfaProcessState<ExplState>, ExplPrec> multiprocInitFunc = new MultiprocInitFunc<>(processIds.stream().map(id -> Map.entry(id, new XcfaProcessInitFunc<>(processes.get(id*-1-1), ExplInitFunc.create(solver, True())))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
//        final MultiprocTransFunc<XcfaProcessState<ExplState>, XcfaProcessAction, ExplPrec> multiprocTransFunc = new MultiprocTransFunc<>(processIds.stream().map(id -> Map.entry(id, new XcfaProcessTransFunc<>(ExplStmtTransFunc.create(solver, 0)))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
//        final XcfaProcessPartialOrd<ExplState> partialOrd = new XcfaProcessPartialOrd<>(ExplOrd.getInstance());
//        final MCM mcm = CatDslManager.createMCM(new File(getClass().getResource(mcmFilename).getFile()));
//        final List<MemoryEvent.Write> initialWrites = xcfa.getvars().stream().filter(it -> xcfa.getInitValue(it).isPresent()).map(it -> new MemoryEvent.Write(memEventProvider.getVarId(it), it, null,  Set.of(), null)).collect(Collectors.toList());
//
//        final MCMChecker<XcfaProcessState<ExplState>, XcfaProcessAction, ExplPrec> mcmChecker = new MCMChecker<>(memEventProvider, multiprocLTS, multiprocInitFunc, multiprocTransFunc, processIds, initialWrites, partialOrd, ExplState.top(), solver, mcm, NullLogger.getInstance());
//        mcmChecker.check(ExplPrec.empty());
    }
}
