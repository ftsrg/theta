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
package hu.bme.mit.theta.solver.z3;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import com.microsoft.z3.Native;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpMarkerTree;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.solver.parser.ThrowExceptionErrorListener;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

final class Z3ItpSolver implements ItpSolver, Solver {

    private final Z3TransformationManager transformationManager;

    private final com.microsoft.z3.Context z3Context;
    private final Z3Solver solver;

    private final Stack<Z3ItpMarker> markers;

    private final Stack<ConstDecl<?>> declarationStack;

    private final GenericSmtLibSymbolTable smtLibSymbolTable;
    private final SmtLibTransformationManager smtLibTransformationManager;
    private final SmtLibTermTransformer smtLibTermTransformer;

    public Z3ItpSolver(
            final Z3SymbolTable symbolTable,
            final Z3TransformationManager transformationManager,
            final Z3TermTransformer termTransformer,
            final com.microsoft.z3.Context z3Context,
            final com.microsoft.z3.Solver z3Solver) {
        this.transformationManager = transformationManager;
        this.z3Context = z3Context;

        solver =
                new Z3Solver(
                        symbolTable, transformationManager, termTransformer, z3Context, z3Solver);

        markers = new StackImpl<>();
        declarationStack = new StackImpl<>();

        smtLibSymbolTable = new GenericSmtLibSymbolTable();
        smtLibTransformationManager = new GenericSmtLibTransformationManager(smtLibSymbolTable);
        smtLibTermTransformer = new GenericSmtLibTermTransformer(smtLibSymbolTable);
    }

    @Override
    public ItpPattern createTreePattern(final ItpMarkerTree<? extends ItpMarker> root) {
        checkNotNull(root);
        return Z3ItpPattern.of(root);
    }

    @Override
    public Z3ItpMarker createMarker() {
        final Z3ItpMarker marker = new Z3ItpMarker();
        markers.add(marker);
        return marker;
    }

    @Override
    public void add(final ItpMarker marker, final Expr<BoolType> assertion) {
        checkNotNull(marker);
        checkNotNull(assertion);
        checkArgument(markers.toCollection().contains(marker), "Marker not found in solver");
        final Z3ItpMarker z3Marker = (Z3ItpMarker) marker;
        final com.microsoft.z3.BoolExpr term =
                (com.microsoft.z3.BoolExpr) transformationManager.toTerm(assertion);
        solver.add(assertion, term);
        z3Marker.add(assertion);
    }

    @Override
    public Interpolant getInterpolant(final ItpPattern pattern) {
        checkState(
                solver.getStatus() == SolverStatus.UNSAT,
                "Cannot get interpolant if status is not UNSAT.");
        checkArgument(pattern instanceof Z3ItpPattern);
        final Z3ItpPattern z3ItpPattern = (Z3ItpPattern) pattern;
        final List<Z3ItpMarker> markers = z3ItpPattern.getSequence();

        final List<Z3ItpMarker> A = new ArrayList<>();
        final List<Z3ItpMarker> B = new ArrayList<>(markers);

        final Map<ItpMarker, Expr<BoolType>> itpMap = new HashMap<>();
        for (final var marker : markers) {
            B.remove(marker);
            A.add(marker);

            if (B.size() != 0) {
                final var localConstDecls = new LinkedHashSet<ConstDecl<?>>();
                final var aTerm =
                        A.stream()
                                .flatMap(m -> m.getTerms().stream())
                                .peek(
                                        boolTypeExpr ->
                                                localConstDecls.addAll(
                                                        ExprUtils.getConstants(boolTypeExpr)))
                                .map(smtLibTransformationManager::toTerm);
                final var bTerm =
                        B.stream()
                                .flatMap(m -> m.getTerms().stream())
                                .peek(
                                        boolTypeExpr ->
                                                localConstDecls.addAll(
                                                        ExprUtils.getConstants(boolTypeExpr)))
                                .map(smtLibTransformationManager::toTerm);

                final var smtLibString =
                        String.format(
                                "(get-interpolant (and %s) (and %s))",
                                aTerm.collect(Collectors.joining(" ")),
                                bTerm.collect(Collectors.joining(" ")));

                localConstDecls.removeAll(declarationStack.toCollection());
                declarationStack.add(localConstDecls);

                final var smtLibDeclString =
                        localConstDecls.stream()
                                .map(smtLibSymbolTable::getDeclaration)
                                .collect(Collectors.joining(" "));

                Native.evalSmtlib2String(z3Context.nCtx(), smtLibDeclString);
                final var response = Native.evalSmtlib2String(z3Context.nCtx(), smtLibString);

                itpMap.put(
                        marker,
                        smtLibTermTransformer.toExpr(
                                parseItpResponse(response),
                                Bool(),
                                new SmtLibModel(Collections.emptyMap())));
            } else {
                itpMap.put(marker, False());
            }
        }
        return new Z3Interpolant(itpMap);
    }

    private static String parseItpResponse(final String response) {
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
    public Collection<? extends ItpMarker> getMarkers() {
        return markers.toCollection();
    }

    // delegate

    @Override
    public void add(final Expr<BoolType> assertion) {
        checkNotNull(assertion);
        solver.add(assertion);
    }

    @Override
    public SolverStatus check() {
        return solver.check();
    }

    @Override
    public void push() {
        markers.push();
        for (final Z3ItpMarker marker : markers) {
            marker.push();
        }
        //        declarationStack.push();
        solver.push();
    }

    @Override
    public void pop(final int n) {
        markers.pop(n);
        for (final Z3ItpMarker marker : markers) {
            marker.pop(n);
        }
        //        declarationStack.pop(n);
        solver.pop(n);
    }

    @Override
    public void reset() {
        solver.reset();
    }

    @Override
    public SolverStatus getStatus() {
        return solver.getStatus();
    }

    @Override
    public Valuation getModel() {
        return solver.getModel();
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return solver.getAssertions();
    }

    @Override
    public void close() {
        solver.close();
    }
}
