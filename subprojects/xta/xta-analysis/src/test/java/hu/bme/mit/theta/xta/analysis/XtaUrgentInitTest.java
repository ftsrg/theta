/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import static hu.bme.mit.theta.analysis.algorithm.arg.SearchStrategy.BFS;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.google.common.collect.Iterables;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.DataStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaCheckerFactory;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * In each model, {@code err} is behind {@code guard x > 0} from the initial location {@code init0},
 * so it is reachable only if time may elapse in {@code init0}: not when it is urgent or committed.
 */
public final class XtaUrgentInitTest {

    private static final String MODEL_NORMAL = "/normal-init.xta";
    private static final List<String> MODELS =
            List.of("/urgent-init.xta", "/committed-init.xta", MODEL_NORMAL);

    public static Collection<String> models() {
        return MODELS;
    }

    public static Collection<Object[]> modelsAndClockStrategies() {
        final Collection<Object[]> result = new ArrayList<>();
        for (final String model : MODELS) {
            for (final ClockStrategy clockStrategy : ClockStrategy.values()) {
                result.add(new Object[] {model, clockStrategy});
            }
        }
        return result;
    }

    @MethodSource("models")
    @ParameterizedTest(name = "{0}")
    public void testInitZone(final String model) throws IOException {
        final XtaSystem system = load(model);
        final ZonePrec prec = ZonePrec.of(system.getClockVars());
        final ZoneState initZone =
                Iterables.getOnlyElement(
                        XtaZoneAnalysis.create(system).getInitFunc().getInitStates(prec));
        final ZoneState zero = ZoneState.zero(system.getClockVars());

        assertTrue(zero.isLeq(initZone));
        assertEquals(model.equals(MODEL_NORMAL), !initZone.isLeq(zero));
    }

    @MethodSource("modelsAndClockStrategies")
    @ParameterizedTest(name = "model: {0}, clock: {1}")
    public void testErrReachability(final String model, final ClockStrategy clockStrategy)
            throws IOException {
        final XtaSystem system = load(model);
        final SafetyChecker<
                        ? extends ARG<? extends XtaState<?>, XtaAction>,
                        ? extends Trace<? extends XtaState<?>, XtaAction>,
                        UnitPrec>
                checker =
                        LazyXtaCheckerFactory.create(system, DataStrategy.NONE, clockStrategy, BFS);
        final SafetyResult<
                        ? extends ARG<? extends XtaState<?>, XtaAction>,
                        ? extends Trace<? extends XtaState<?>, XtaAction>>
                result = checker.check(UnitPrec.getInstance());

        final boolean errReached =
                result.getProof()
                        .getNodes()
                        .anyMatch(
                                n ->
                                        n.getState().getLocs().stream()
                                                .anyMatch(l -> l.getName().equals("P_err")));
        assertEquals(model.equals(MODEL_NORMAL), errReached);
    }

    private XtaSystem load(final String model) throws IOException {
        try (InputStream inputStream = getClass().getResourceAsStream(model)) {
            return XtaDslManager.createSystem(inputStream);
        }
    }
}
