package hu.bme.mit.theta.xcfa.analysis.impl.lazy;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorResult;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.ExprMeetStrategy;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAction;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.utils.FrontendXcfaBuilder;
import hu.bme.mit.theta.xcfa.passes.procedurepass.ProcedurePass;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
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
import java.util.Objects;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.analysis.algorithm.SearchStrategy.BFS;
import static org.junit.Assert.assertTrue;

@RunWith(Parameterized.class)
public final class LazyXcfaAbstractorTest {

    private static final Collection<Tuple2<String, Boolean>> MODELS = ImmutableList.of(
            Tuple2.of("/00assignment.c", false),
            Tuple2.of("/counter5_true.c", true),
            Tuple2.of("/counter5_false.c", false)
    );

    @Parameter(0)
    public String filepath;

    @Parameter(1)
    public boolean safe;

    @Parameter(2)
    public DataStrategy2 dataStrategy;

    private LazyXcfaAbstractorConfig<ExprState, ExprState, XcfaAction, Prec> abstractor;

    @Parameters(name = "model: {0}, safe: {1}, strategy: {2}")
    public static Collection<Object[]> data() {
        final Collection<Object[]> result = new ArrayList<>();
        for (final Tuple2<String, Boolean> model : MODELS) {
            for (final DataStrategy2 dataStrategy : DataStrategy2.getValidStrategies()) {
                result.add(new Object[]{model.get1(), model.get2(), dataStrategy});
            }
        }
        return result;
    }

    @Before
    public void initialize() throws IOException {
        ArchitectureConfig.arithmetic = ArchitectureConfig.ArithmeticType.efficient;
        ArchitectureConfig.multiThreading = false;
        FrontendMetadata.clear();
        ProcedurePass.postInlining = false;

        final InputStream inputStream = getClass().getResourceAsStream(filepath);
        final CharStream input = CharStreams.fromStream(Objects.requireNonNull(inputStream));
        final CLexer lexer = new CLexer(input);
        final CommonTokenStream tokens = new CommonTokenStream(lexer);
        final CParser parser = new CParser(tokens);
        final CParser.CompilationUnitContext context = parser.compilationUnit();

        final CStatement program = context.accept(FunctionVisitor.instance);
        checkState(program instanceof CProgram, "Parsing did not return a program!");
        final FrontendXcfaBuilder frontendXcfaBuilder = new FrontendXcfaBuilder();
        final XCFA xcfa1 = new FrontendXcfaBuilder().buildXcfa((CProgram) program).build();

        abstractor = LazyXcfaAbstractorConfigFactory.create(xcfa1, dataStrategy, BFS, ExprMeetStrategy.SYNTACTIC);
    }

    @Test
    public void test() {
        test(abstractor);
    }

    private void test(LazyXcfaAbstractorConfig<ExprState, ExprState, XcfaAction, Prec> abstractor) {
        // Act
        final AbstractorResult result = abstractor.check();

        // Assert
        if(safe) {
            assertTrue(result.isSafe());
        } else {
            assertTrue(result.isUnsafe());
        }

        final ArgChecker argChecker = ArgChecker.create(Z3SolverFactory.getInstance().createSolver());
        final boolean argCheckResult = argChecker.isWellLabeled(abstractor.getArg());
        assertTrue(argCheckResult);
    }
}
