package hu.bme.mit.theta.xta.analysis;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.DataStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaAbstractorFactory;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;

import static hu.bme.mit.theta.analysis.algorithm.SearchStrategy.BFS;
import static hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy.LU;
import static org.junit.Assert.assertTrue;

@RunWith(Parameterized.class)
public final class LazyXtaAbstractorTest {
    private static final String MODEL_CSMA = "/csma-2.xta";
    private static final String MODEL_FDDI = "/fddi-2.xta";
    private static final String MODEL_FISCHER = "/fischer-2-32-64.xta";
    private static final String MODEL_LYNCH = "/lynch-2-16.xta";
    private static final String MODEL_ENGINE = "/engine-classic.xta";
    private static final String MODEL_BROADCAST = "/broadcast.xta";

    private static final Collection<String> MODELS = ImmutableList.of(MODEL_CSMA, MODEL_FDDI, MODEL_FISCHER,
            MODEL_LYNCH, MODEL_ENGINE, MODEL_BROADCAST);

    private static final Collection<String> MODELS_WITH_UNKNOWN_SOLVER_STATUS = ImmutableSet.of(MODEL_FDDI,
            MODEL_ENGINE, MODEL_BROADCAST);

    @Parameter(0)
    public String filepath;

    @Parameter(1)
    public DataStrategy dataStrategy;

    @Parameter(2)
    public ClockStrategy clockStrategy;

    private Abstractor<? extends LazyState<?, ?>, XtaAction, UnitPrec> abstractor;

    @Parameters(name = "model: {0}, discrete: {1}, clock: {2}")
    public static Collection<Object[]> data() {
        final Collection<Object[]> result = new ArrayList<>();
        for (final String model : MODELS) {
            for (final DataStrategy dataStrategy : DataStrategy.values()) {
                for (final ClockStrategy clockStrategy : ClockStrategy.values()) {
                    if (!MODELS_WITH_UNKNOWN_SOLVER_STATUS.contains(model) || (clockStrategy != LU)) {
                        result.add(new Object[]{model, dataStrategy, clockStrategy});
                    }
                }
            }
        }
        return result;
    }

    @Before
    public void initialize() throws IOException {
        final InputStream inputStream = getClass().getResourceAsStream(filepath);
        final XtaSystem system = XtaDslManager.createSystem(inputStream);
        abstractor = LazyXtaAbstractorFactory.create(system, dataStrategy, clockStrategy, BFS);
    }

    @Test
    public void test() {
        test(abstractor);
    }

    private <S extends LazyState<?, ?>> void test(Abstractor<S, XtaAction, UnitPrec> abstractor) {
        // Act
        final ARG<S, XtaAction> arg = abstractor.createArg();
        abstractor.check(arg, UnitPrec.getInstance());

        // Assert
        final ArgChecker argChecker = ArgChecker.create(Z3SolverFactory.getInstance().createSolver());
        final boolean argCheckResult = argChecker.isWellLabeled(arg);
        assertTrue(argCheckResult);
    }
}
