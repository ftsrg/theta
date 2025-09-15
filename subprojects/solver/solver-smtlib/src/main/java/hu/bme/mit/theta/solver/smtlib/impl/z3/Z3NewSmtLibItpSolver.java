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
package hu.bme.mit.theta.solver.smtlib.impl.z3;

import static com.google.common.base.Preconditions.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.*;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibItpSolver;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.solver.interpolation.SmtLibInterpolant;
import hu.bme.mit.theta.solver.smtlib.solver.interpolation.SmtLibItpPattern;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.solver.parser.ThrowExceptionErrorListener;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;
import java.util.*;
import java.util.stream.Collectors;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

public class Z3NewSmtLibItpSolver extends SmtLibItpSolver<Z3SmtLibItpMarker> {

    private final Map<Expr<BoolType>, String> assertionNames = new HashMap<>();
    private static final String assertionNamePattern = "_z3_assertion_%d";
    private static long assertionCount = 0;

    public Z3NewSmtLibItpSolver(
            final SmtLibSymbolTable symbolTable,
            final SmtLibTransformationManager transformationManager,
            final SmtLibTermTransformer termTransformer,
            final SmtLibSolverBinary solverBinary) {
        super(symbolTable, transformationManager, termTransformer, solverBinary);
    }

    @Override
    public ItpPattern createTreePattern(ItpMarkerTree<? extends ItpMarker> root) {
        checkNotNull(root);
        return SmtLibItpPattern.of(root);
    }

    @Override
    public Z3SmtLibItpMarker createMarker() {
        final var marker = new Z3SmtLibItpMarker();
        markers.add(marker);
        return marker;
    }

    @Override
    protected void add(
            Z3SmtLibItpMarker marker,
            Expr<BoolType> assertion,
            Set<ConstDecl<?>> consts,
            String term) {
        consts.stream().map(symbolTable::getDeclaration).forEach(this::issueGeneralCommand);

        final var name = String.format(assertionNamePattern, assertionCount++);
        assertionNames.put(assertion, name);
        issueGeneralCommand(String.format("(assert (! %s :named %s))", term, name));
    }

    @Override
    public Interpolant getInterpolant(ItpPattern pattern) {
        checkState(
                getStatus() == SolverStatus.UNSAT,
                "Cannot get interpolant if status is not UNSAT.");
        checkArgument(pattern instanceof SmtLibItpPattern);
        @SuppressWarnings("unchecked")
        final var z3ItpPattern = (SmtLibItpPattern<Z3SmtLibItpMarker>) pattern;
        final List<Z3SmtLibItpMarker> markers = z3ItpPattern.getSequence();

        final List<Z3SmtLibItpMarker> A = new ArrayList<>();
        final List<Z3SmtLibItpMarker> B = new ArrayList<>(markers);

        final Map<ItpMarker, Expr<BoolType>> itpMap = new HashMap<>();
        for (final var marker : markers) {
            B.remove(marker);
            A.add(marker);

            if (B.size() != 0) {
                final var aTerm =
                        A.stream()
                                .flatMap(m -> m.getTerms().stream().map(Tuple2::get1))
                                .map(assertionNames::get);
                final var bTerm =
                        B.stream()
                                .flatMap(m -> m.getTerms().stream().map(Tuple2::get1))
                                .map(assertionNames::get);

                solverBinary.issueCommand(
                        String.format(
                                "(get-interpolant (and %s) (and %s))",
                                aTerm.collect(Collectors.joining(" ")),
                                bTerm.collect(Collectors.joining(" "))));

                itpMap.put(
                        marker,
                        termTransformer.toExpr(
                                parseItpResponse(solverBinary.readResponse()),
                                Bool(),
                                new SmtLibModel(Collections.emptyMap())));
            } else {
                itpMap.put(marker, False());
            }
        }

        return new SmtLibInterpolant(itpMap);
    }

    private String parseItpResponse(final String response) {
        final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(response));
        final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
        try {
            lexer.removeErrorListeners();
            lexer.addErrorListener(new ThrowExceptionErrorListener());
            parser.removeErrorListeners();
            parser.addErrorListener(new ThrowExceptionErrorListener());
            return extractString(parser.term());
        } catch (Exception e) {
            try {
                throw new SmtLibSolverException(
                        parser.response().general_response_error().reason.getText());
            } catch (Exception ex) {
                throw new SmtLibSolverException("Could not parse solver output: " + response, e);
            }
        }
    }

    private static String extractString(final ParserRuleContext ctx) {
        return ctx.start
                .getInputStream()
                .getText(new Interval(ctx.start.getStartIndex(), ctx.stop.getStopIndex()));
    }

    @Override
    protected void init() {
        issueGeneralCommand("(set-option :print-success true)");
        issueGeneralCommand("(set-option :produce-models true)");
        // issueGeneralCommand("(set-option :produce-interpolants true)");
        issueGeneralCommand("(set-logic ALL)");
    }
}
