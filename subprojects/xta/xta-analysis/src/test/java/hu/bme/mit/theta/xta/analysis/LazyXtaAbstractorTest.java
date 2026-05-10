package hu.bme.mit.theta.xta.analysis;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgChecker;
import hu.bme.mit.theta.analysis.expr.ExprLattice;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.lazy.*;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import static hu.bme.mit.theta.analysis.algorithm.arg.SearchStrategy.BFS;
import static hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy.LU;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class LazyXtaAbstractorTest {

    private static final String MODEL_CSMA = "/model/csma-2.xta";
    private static final String MODEL_FDDI = "/model/fddi-2.xta";
    private static final String MODEL_FISCHER = "/model/fischer-2-32-64.xta";
    private static final String MODEL_LYNCH = "/model/lynch-2-16.xta";
    private static final String MODEL_ENGINE = "/model/engine-classic.xta";
    private static final String MODEL_BROADCAST = "/model/broadcast.xta";

    private static final Collection<String> MODELS =
        ImmutableList.of(
            MODEL_CSMA,
            MODEL_FDDI,
            MODEL_FISCHER,
            MODEL_LYNCH,
            MODEL_ENGINE,
            MODEL_BROADCAST);

    private static final Collection<String> MODELS_WITH_UNKNOWN_SOLVER_STATUS =
        ImmutableSet.of(MODEL_FDDI, MODEL_ENGINE, MODEL_BROADCAST);

    public String filepath;
    public DataStrategy dataStrategy;
    public ClockStrategy clockStrategy;

    private LazyXtaCheckerConfig<?, ?, ?> abstractor;

    public static Collection<Object[]> data() {
        final Collection<Object[]> result = new ArrayList<>();
        for (final String model : MODELS) {

            for (final DataStrategy dataStrategy : DataStrategy.getValidStrategies()) {
                for (final ClockStrategy clockStrategy : ClockStrategy.values()) {
                    if (!MODELS_WITH_UNKNOWN_SOLVER_STATUS.contains(model) || (clockStrategy != LU)) {
                        result.add(new Object[]{model, dataStrategy, clockStrategy});
                    }
                }
            }
        }
        return result;
    }

    public void initialize() throws IOException {
        final InputStream inputStream = getClass().getResourceAsStream(filepath);
        final XtaSystem system = XtaDslManager.createSystem(inputStream);
        abstractor = LazyXtaCheckerConfigFactory.create(
            system,
            new ConsoleLogger(Logger.Level.DETAIL),
            dataStrategy,
            clockStrategy,
            BFS,
            ExprLattice.MeetImpl.SYNTACTIC_CHECK
        );
    }

    @MethodSource("data")
    @ParameterizedTest(name = "model: {0}, discrete: {1}, clock: {2}")
    public void test(String filepath, DataStrategy dataStrategy, ClockStrategy clockStrategy)
            throws IOException {
        initLazyXtaAbstractorTest(filepath, dataStrategy, clockStrategy);
        test(abstractor);
    }

    private void test(LazyXtaCheckerConfig<?, ?, ?> config) throws IOException {
        // Act
        final var result = config.check();

        // Assert
        final ArgChecker argChecker =
            ArgChecker.create(Z3LegacySolverFactory.getInstance().createSolver());
        final boolean argCheckResult = argChecker.isWellLabeled(result.getProof());
        assertTrue(argCheckResult);
    }

    public void initLazyXtaAbstractorTest(
        String filepath, DataStrategy dataStrategy, ClockStrategy clockStrategy)
            throws IOException {
        this.filepath = filepath;
        this.dataStrategy = dataStrategy;
        this.clockStrategy = clockStrategy;
        this.initialize();
    }
}
