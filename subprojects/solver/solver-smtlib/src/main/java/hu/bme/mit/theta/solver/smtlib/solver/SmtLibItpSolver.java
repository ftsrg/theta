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
package hu.bme.mit.theta.solver.smtlib.solver;

import static com.google.common.base.Preconditions.*;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.*;
import hu.bme.mit.theta.solver.impl.StackImpl;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.solver.interpolation.SmtLibItpMarker;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibValuation;
import hu.bme.mit.theta.solver.smtlib.solver.parser.CheckSatResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GeneralResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GetModelResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.ThrowExceptionErrorListener;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;
import java.util.Collection;
import java.util.Set;
import java.util.stream.Collectors;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

public abstract class SmtLibItpSolver<T extends SmtLibItpMarker> implements ItpSolver {

    protected final SmtLibSymbolTable symbolTable;
    protected final SmtLibTransformationManager transformationManager;
    protected final SmtLibTermTransformer termTransformer;

    protected final SmtLibSolverBinary solverBinary;

    protected final Stack<Expr<BoolType>> assertions;
    protected final Stack<T> markers;
    protected final Stack<ConstDecl<?>> declarationStack;
    protected final Stack<EnumType> typeStack;
    protected final SmtLibEnumStrategy enumStrategy;

    private Valuation model;
    private SolverStatus status;

    private int expCnt = 0;

    public SmtLibItpSolver(
            final SmtLibSymbolTable symbolTable,
            final SmtLibTransformationManager transformationManager,
            final SmtLibTermTransformer termTransformer,
            final SmtLibSolverBinary solverBinary) {
        this(
                symbolTable,
                transformationManager,
                termTransformer,
                solverBinary,
                SmtLibEnumStrategy.getDefaultStrategy());
    }

    public SmtLibItpSolver(
            final SmtLibSymbolTable symbolTable,
            final SmtLibTransformationManager transformationManager,
            final SmtLibTermTransformer termTransformer,
            final SmtLibSolverBinary solverBinary,
            final SmtLibEnumStrategy enumStrategy) {
        this.symbolTable = symbolTable;
        this.transformationManager = transformationManager;
        this.termTransformer = termTransformer;
        this.enumStrategy = enumStrategy;

        this.solverBinary = solverBinary;

        this.assertions = new StackImpl<>();
        this.markers = new StackImpl<>();
        this.declarationStack = new StackImpl<>();
        typeStack = new StackImpl<>();

        init();
    }

    @Override
    public abstract T createMarker();

    @Override
    public Collection<? extends ItpMarker> getMarkers() {
        return markers.toCollection();
    }

    @SuppressWarnings("unchecked")
    @Override
    public void add(final ItpMarker marker, final Expr<BoolType> assertion) {
        checkNotNull(marker);
        checkNotNull(assertion);
        checkNotNull((T) marker);
        checkArgument(markers.toCollection().contains(marker));

        final var consts = ExprUtils.getConstants(assertion);
        consts.removeAll(declarationStack.toCollection());
        declarationStack.add(consts);
        enumStrategy.declareDatatypes(
                (Collection<Type>) consts.stream().map(ConstDecl::getType).toList(),
                typeStack,
                this::issueGeneralCommand);

        final var itpMarker = (T) marker;
        final var term = transformationManager.toTerm(assertion);

        itpMarker.add(
                assertion,
                enumStrategy.wrapAssertionExpression(
                        term,
                        ExprUtils.getConstants(assertion).stream()
                                .collect(Collectors.toMap(c -> c, symbolTable::getSymbol))));

        assertions.add(assertion);
        add(
                itpMarker,
                assertion,
                consts,
                enumStrategy.wrapAssertionExpression(
                        term,
                        ExprUtils.getConstants(assertion).stream()
                                .collect(Collectors.toMap(c -> c, symbolTable::getSymbol))));

        clearState();
    }

    protected abstract void add(
            final T marker,
            final Expr<BoolType> assertion,
            final Set<ConstDecl<?>> consts,
            final String term);

    @Override
    public SolverStatus check() {
        solverBinary.issueCommand("(check-sat)");
        var res = parseResponse(solverBinary.readResponse());
        if (res.isError()) {
            throw new SmtLibSolverException(res.getReason());
        } else if (res.isSpecific()) {
            final CheckSatResponse checkSatResponse = res.asSpecific().asCheckSatResponse();
            if (checkSatResponse.isSat()) {
                status = SolverStatus.SAT;
            } else if (checkSatResponse.isUnsat()) {
                status = SolverStatus.UNSAT;
            } else {
                throw new UnknownSolverStatusException();
            }
        } else {
            throw new AssertionError();
        }

        return status;
    }

    @Override
    public void push() {
        expCnt++;
        markers.push();
        for (final var marker : markers) {
            marker.push();
        }
        assertions.push();
        declarationStack.push();
        typeStack.push();
        issueGeneralCommand("(push 1)");
    }

    @Override
    public void pop(final int n) {
        expCnt -= n;
        markers.pop(n);
        for (final var marker : markers) {
            marker.pop(n);
        }
        assertions.pop(n);
        declarationStack.pop(n);
        typeStack.pop(n);
        issueGeneralCommand(String.format("(pop %d)", n));
        clearState();
    }

    @Override
    public void popAll() {
        pop(expCnt);
    }

    @Override
    public void reset() {
        expCnt = 0;
        issueGeneralCommand("(reset)");
        clearState();
        init();
    }

    @Override
    public SolverStatus getStatus() {
        checkState(status != null, "Solver status is unknown.");
        return status;
    }

    @Override
    public Valuation getModel() {
        checkState(status == SolverStatus.SAT, "Cannot get model if status is not SAT.");

        if (model == null) {
            model = extractModel();
        }

        return model;
    }

    private Valuation extractModel() {
        assert status == SolverStatus.SAT;
        assert model == null;

        solverBinary.issueCommand("(get-model)");
        final var res = parseResponse(solverBinary.readResponse());
        if (res.isError()) {
            throw new SmtLibSolverException(res.getReason());
        } else if (res.isSpecific()) {
            final GetModelResponse getModelResponse = res.asSpecific().asGetModelResponse();
            return new SmtLibValuation(
                    symbolTable,
                    transformationManager,
                    termTransformer,
                    getModelResponse.getModel());
        } else {
            throw new AssertionError();
        }
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return assertions.toCollection();
    }

    @Override
    public void close() throws Exception {
        solverBinary.close();
    }

    protected void clearState() {
        status = null;
        model = null;
    }

    protected void init() {
        issueGeneralCommand("(set-option :print-success true)");
        issueGeneralCommand("(set-option :produce-models true)");
        issueGeneralCommand("(set-logic ALL)");
    }

    protected final void issueGeneralCommand(String command) {
        solverBinary.issueCommand(command);
        var res = parseResponse(solverBinary.readResponse());
        if (res.isError()) {
            throw new SmtLibSolverException(res.getReason());
        }
    }

    protected final GeneralResponse parseResponse(final String response) {
        try {
            final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(response));
            final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
            lexer.removeErrorListeners();
            lexer.addErrorListener(new ThrowExceptionErrorListener());
            parser.removeErrorListeners();
            parser.addErrorListener(new ThrowExceptionErrorListener());
            return GeneralResponse.fromContext(parser.response());
        } catch (Exception e) {
            throw new SmtLibSolverException("Could not parse solver output: " + response, e);
        }
    }
}
