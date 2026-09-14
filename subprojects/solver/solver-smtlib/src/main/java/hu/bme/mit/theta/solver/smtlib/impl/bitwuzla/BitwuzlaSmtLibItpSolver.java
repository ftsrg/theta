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
package hu.bme.mit.theta.solver.smtlib.impl.bitwuzla;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpMarkerTree;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.SolverStatus;
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
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

/**
 * Interpolating solver over bitwuzla's {@code (get-interpolant (<name>...))}, which takes the names
 * of the assertions forming the A side and interpolates them against <em>every</em> other assertion
 * in the solver. That is binary interpolation only; sequence patterns are decomposed into binary
 * queries the same way the CVC5 and new Z3 drivers do.
 */
public final class BitwuzlaSmtLibItpSolver extends SmtLibItpSolver<BitwuzlaSmtLibItpMarker> {

    private static final String ASSERTION_NAME_PATTERN = "_bitwuzla_itp_%d";

    private long assertionCount = 0;

    public BitwuzlaSmtLibItpSolver(
            final SmtLibSymbolTable symbolTable,
            final SmtLibTransformationManager transformationManager,
            final SmtLibTermTransformer termTransformer,
            final SmtLibSolverBinary solverBinary) {
        super(symbolTable, transformationManager, termTransformer, solverBinary);
    }

    @Override
    public ItpPattern createTreePattern(final ItpMarkerTree<? extends ItpMarker> root) {
        checkNotNull(root);
        return SmtLibItpPattern.of(root);
    }

    @Override
    public BitwuzlaSmtLibItpMarker createMarker() {
        final var marker = new BitwuzlaSmtLibItpMarker();
        markers.add(marker);
        return marker;
    }

    @Override
    protected void add(
            final BitwuzlaSmtLibItpMarker marker,
            final Expr<BoolType> assertion,
            final Set<ConstDecl<?>> consts,
            final String term) {
        consts.stream().map(symbolTable::getDeclaration).forEach(this::issueGeneralCommand);

        final var name = String.format(ASSERTION_NAME_PATTERN, assertionCount++);
        marker.addAssertionName(name);
        issueGeneralCommand(String.format("(assert (! %s :named %s))", term, name));
    }

    /**
     * Interpolates every prefix of the pattern against the rest of it, as the CVC5 and new Z3
     * drivers do. The results are therefore binary interpolants for each cut, and NOT an inductive
     * sequence interpolant: nothing here forces {@code itp(I_k) and F_(k+1) => itp(I_k+1)}, since
     * the cuts are solved independently.
     */
    @Override
    public Interpolant getInterpolant(final ItpPattern pattern) {
        checkState(
                getStatus() == SolverStatus.UNSAT,
                "Cannot get interpolant if status is not UNSAT.");
        checkArgument(pattern instanceof SmtLibItpPattern);
        @SuppressWarnings("unchecked")
        final var bitwuzlaItpPattern = (SmtLibItpPattern<BitwuzlaSmtLibItpMarker>) pattern;

        checkBranchFree(bitwuzlaItpPattern.getRoot());
        final List<BitwuzlaSmtLibItpMarker> markerSequence = bitwuzlaItpPattern.getSequence();
        checkOnlyPatternMarkersAsserted(markerSequence);

        final List<BitwuzlaSmtLibItpMarker> A = new ArrayList<>();
        final List<BitwuzlaSmtLibItpMarker> B = new ArrayList<>(markerSequence);

        final Map<ItpMarker, Expr<BoolType>> itpMap = new HashMap<>();
        for (final var marker : markerSequence) {
            B.remove(marker);
            A.add(marker);

            if (B.size() != 0) {
                itpMap.put(marker, interpolateAgainstTheRest(A));
            } else {
                itpMap.put(marker, False());
            }
        }

        return new SmtLibInterpolant(itpMap);
    }

    /** A branching tree cannot be cut into prefixes, which is what the binary queries need. */
    private void checkBranchFree(final ItpMarkerTree<BitwuzlaSmtLibItpMarker> root) {
        for (var node = root; node.getChildrenNumber() > 0; node = node.getChild(0)) {
            if (node.getChildrenNumber() > 1) {
                throw new UnsupportedOperationException(
                        String.format(
                                "Bitwuzla builds interpolants from binary queries, so it supports"
                                        + " sequence patterns only, but the given pattern branches"
                                        + " into %d subtrees",
                                node.getChildrenNumber()));
            }
        }
    }

    /**
     * The B side of a bitwuzla query is everything that is not named in it, so an assertion held by
     * a marker outside the pattern would silently join B and make the interpolant useless. The CVC5
     * and Z3 drivers name both sides explicitly and so need no such check.
     */
    private void checkOnlyPatternMarkersAsserted(
            final List<BitwuzlaSmtLibItpMarker> markerSequence) {
        for (final var marker : markers.toCollection()) {
            if (!markerSequence.contains(marker) && !marker.getAssertionNames().isEmpty()) {
                throw new UnsupportedOperationException(
                        "Bitwuzla interpolates the named group against every other assertion, so"
                                + " markers outside the pattern must be empty");
            }
        }
    }

    private Expr<BoolType> interpolateAgainstTheRest(final List<BitwuzlaSmtLibItpMarker> A) {
        final var names =
                A.stream()
                        .flatMap(marker -> marker.getAssertionNames().stream())
                        .collect(Collectors.toUnmodifiableList());
        if (names.isEmpty()) {
            return True(); // bitwuzla rejects an empty group, and the interpolant of true is true
        }

        solverBinary.issueCommand(String.format("(get-interpolant (%s))", String.join(" ", names)));
        return termTransformer.toExpr(
                parseItpResponse(solverBinary.readResponse()),
                Bool(),
                new SmtLibModel(Collections.emptyMap()));
    }

    @Override
    protected void init() {
        super.init();
        issueGeneralCommand("(set-option :produce-interpolants true)");
    }

    private String parseItpResponse(final String response) {
        if (response.startsWith("[error]")) { // bitwuzla reports on stderr, then exits
            throw new SmtLibSolverException(response);
        }

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
}
