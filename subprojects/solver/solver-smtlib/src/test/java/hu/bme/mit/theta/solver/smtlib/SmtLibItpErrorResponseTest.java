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
package hu.bme.mit.theta.solver.smtlib;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Named.named;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.smtlib.impl.bitwuzla.BitwuzlaSmtLibItpSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager;
import hu.bme.mit.theta.solver.smtlib.impl.mathsat.MathSATSmtLibItpSolver;
import hu.bme.mit.theta.solver.smtlib.impl.mathsat.MathSATSmtLibTransformationManager;
import hu.bme.mit.theta.solver.smtlib.impl.z3.Z3NewSmtLibItpSolver;
import hu.bme.mit.theta.solver.smtlib.impl.z3.Z3OldSmtLibItpSolver;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary;
import java.util.function.Function;
import java.util.stream.Stream;
import org.junit.jupiter.api.Named;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/** The answer to an interpolation query is read as a term, which a solver error also parses as. */
public final class SmtLibItpErrorResponseTest {

    private static final String REASON = "arr: proof splitting not supported";

    /** Answers every command the way a solver does that has found the assertions unsatisfiable. */
    private static final class ScriptedBinary implements SmtLibSolverBinary {

        private final String interpolantResponse;
        private String lastCommand = "";

        private ScriptedBinary(final String interpolantResponse) {
            this.interpolantResponse = interpolantResponse;
        }

        @Override
        public void issueCommand(final String command) {
            lastCommand = command;
        }

        @Override
        public String readResponse() {
            if (lastCommand.startsWith("(check-sat")) return "unsat";
            if (lastCommand.startsWith("(get-interpolant")) return interpolantResponse;
            return "success";
        }

        @Override
        public void close() {}
    }

    private static Stream<Named<Function<SmtLibSolverBinary, ItpSolver>>> drivers() {
        return Stream.of(
                named(
                        "MathSAT",
                        binary -> {
                            final var symbols = new GenericSmtLibSymbolTable();
                            return new MathSATSmtLibItpSolver(
                                    symbols,
                                    new MathSATSmtLibTransformationManager(symbols),
                                    new GenericSmtLibTermTransformer(symbols),
                                    binary);
                        }),
                named(
                        "Z3 new",
                        binary -> {
                            final var symbols = new GenericSmtLibSymbolTable();
                            return new Z3NewSmtLibItpSolver(
                                    symbols,
                                    new GenericSmtLibTransformationManager(symbols),
                                    new GenericSmtLibTermTransformer(symbols),
                                    binary);
                        }),
                named(
                        "Z3 old",
                        binary -> {
                            final var symbols = new GenericSmtLibSymbolTable();
                            return new Z3OldSmtLibItpSolver(
                                    symbols,
                                    new GenericSmtLibTransformationManager(symbols),
                                    new GenericSmtLibTermTransformer(symbols),
                                    binary);
                        }),
                named(
                        "Bitwuzla",
                        binary -> {
                            final var symbols = new GenericSmtLibSymbolTable();
                            return new BitwuzlaSmtLibItpSolver(
                                    symbols,
                                    new GenericSmtLibTransformationManager(symbols),
                                    new GenericSmtLibTermTransformer(symbols),
                                    binary);
                        }));
    }

    private static Expr<BoolType> interpolate(
            final Function<SmtLibSolverBinary, ItpSolver> driver, final String response) {
        final ItpSolver solver = driver.apply(new ScriptedBinary(response));
        final ItpMarker a = solver.createMarker();
        final ItpMarker b = solver.createMarker();
        final Expr<BoolType> x = Const("x", Bool()).getRef();

        solver.add(a, x);
        solver.add(b, Not(x));
        solver.check();
        return solver.getInterpolant(solver.createBinPattern(a, b)).eval(a);
    }

    @ParameterizedTest
    @MethodSource("drivers")
    public void solverErrorKeepsItsReason(final Function<SmtLibSolverBinary, ItpSolver> driver) {
        final var exception =
                assertThrows(
                        SmtLibSolverException.class,
                        () -> interpolate(driver, "(error \"" + REASON + "\")"));
        assertTrue(exception.getMessage().contains(REASON), exception.getMessage());
    }

    @ParameterizedTest
    @MethodSource("drivers")
    public void interpolantIsAccepted(final Function<SmtLibSolverBinary, ItpSolver> driver) {
        assertEquals(True(), interpolate(driver, "true"));
    }
}
