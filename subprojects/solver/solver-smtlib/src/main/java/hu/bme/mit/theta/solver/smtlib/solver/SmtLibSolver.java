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
package hu.bme.mit.theta.solver.smtlib.solver;

import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.AllSatSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.UnknownSolverStatusException;
import hu.bme.mit.theta.solver.impl.StackImpl;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.impl.generic.SmtLibDereferenceDecls;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibValuation;
import hu.bme.mit.theta.solver.smtlib.solver.parser.CheckSatResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GeneralResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GetModelResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GetUnsatCoreResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.ThrowExceptionErrorListener;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

public class SmtLibSolver implements UCSolver, Solver, AllSatSolver {

    private static final String ASSUMPTION_LABEL = "_LABEL_%d";
    protected final SmtLibSymbolTable symbolTable;
    protected final SmtLibTransformationManager transformationManager;
    protected final SmtLibTermTransformer termTransformer;
    protected final SmtLibSolverBinary solverBinary;
    private final boolean unsatCoreEnabled;
    private final String logic;

    protected final Stack<Expr<BoolType>> assertions;
    protected final Map<String, Expr<BoolType>> assumptions;
    protected final Stack<ConstDecl<?>> declarationStack;
    protected final Stack<EnumType> typeStack;
    protected final SmtLibEnumStrategy enumStrategy;
    private int labelNum = 0;

    protected Valuation model;
    protected Collection<Expr<BoolType>> unsatCore;
    protected SolverStatus status;

    public SmtLibSolver(
            final SmtLibSymbolTable symbolTable,
            final SmtLibTransformationManager transformationManager,
            final SmtLibTermTransformer termTransformer,
            final SmtLibSolverBinary solverBinary,
            boolean unsatCoreEnabled) {
        this(
                symbolTable,
                transformationManager,
                termTransformer,
                solverBinary,
                unsatCoreEnabled,
                SmtLibEnumStrategy.getDefaultStrategy(),
                "ALL");
    }

    public SmtLibSolver(
            final SmtLibSymbolTable symbolTable,
            final SmtLibTransformationManager transformationManager,
            final SmtLibTermTransformer termTransformer,
            final SmtLibSolverBinary solverBinary,
            boolean unsatCoreEnabled,
            final SmtLibEnumStrategy enumStrategy) {
        this(
                symbolTable,
                transformationManager,
                termTransformer,
                solverBinary,
                unsatCoreEnabled,
                enumStrategy,
                "ALL");
    }

    public SmtLibSolver(
            final SmtLibSymbolTable symbolTable,
            final SmtLibTransformationManager transformationManager,
            final SmtLibTermTransformer termTransformer,
            final SmtLibSolverBinary solverBinary,
            boolean unsatCoreEnabled,
            final SmtLibEnumStrategy enumStrategy,
            final String logic) {
        this.solverBinary = solverBinary;
        this.symbolTable = symbolTable;
        this.transformationManager = transformationManager;
        this.termTransformer = termTransformer;
        this.enumStrategy = enumStrategy;

        this.unsatCoreEnabled = unsatCoreEnabled;
        this.logic = logic;

        assertions = new StackImpl<>();
        assumptions = new HashMap<>();
        declarationStack = new StackImpl<>();
        typeStack = new StackImpl<>();

        init();
    }

    @Override
    public void add(Expr<BoolType> assertion) {
        final var simplifiedAssertion = ExprUtils.simplify(assertion);
        final var term = transformationManager.toTerm(simplifiedAssertion);
        add(simplifiedAssertion, term);
    }

    public void add(final Expr<BoolType> assertion, final String term) {
        final var consts =
                ExprUtils.getConstants(assertion).stream()
                        .filter(symbolTable::definesConst)
                        .collect(Collectors.toSet());
        // `deref` is an uninterpreted function whose declaration has no ConstDecl in the assertion;
        // the term transformation registered one per signature, so declare it like any other
        // constant.
        consts.addAll(SmtLibDereferenceDecls.collect(assertion));
        consts.removeAll(declarationStack.toCollection());
        declarationStack.add(consts);

        assertions.add(assertion);
        enumStrategy.declareDatatypes(
                consts.stream().map(ConstDecl::getType).toList(),
                typeStack,
                this::issueGeneralCommand);
        consts.stream().map(symbolTable::getDeclaration).forEach(this::issueGeneralCommand);
        issueGeneralCommand(
                String.format(
                        "(assert %s)",
                        enumStrategy.wrapAssertionExpression(
                                term,
                                ExprUtils.getConstants(assertion).stream()
                                        .filter(symbolTable::definesConst)
                                        .collect(
                                                Collectors.toMap(
                                                        c -> c, symbolTable::getSymbol)))));

        clearState();
    }

    @Override
    public void track(Expr<BoolType> assertion) {
        final var consts = ExprUtils.getConstants(assertion);
        consts.addAll(SmtLibDereferenceDecls.collect(assertion));
        consts.removeAll(declarationStack.toCollection());
        declarationStack.add(consts);

        final var term = transformationManager.toTerm(assertion);
        final var label = String.format(ASSUMPTION_LABEL, labelNum++);
        assumptions.put(label, assertion);
        assertions.add(assertion);

        consts.stream().map(symbolTable::getDeclaration).forEach(this::issueGeneralCommand);
        enumStrategy.declareDatatypes(
                (Collection<Type>) consts.stream().map(ConstDecl::getType).toList(),
                typeStack,
                this::issueGeneralCommand);
        issueGeneralCommand(
                String.format(
                        "(assert (! %s :named %s))",
                        enumStrategy.wrapAssertionExpression(
                                term,
                                ExprUtils.getConstants(assertion).stream()
                                        .collect(Collectors.toMap(c -> c, symbolTable::getSymbol))),
                        label));

        clearState();
    }

    /**
     * Solver specific: only backends whose SMT-LIB dialect has an all-sat command say yes. See
     * {@link AllSatSolver}. Overridden by {@code MathSATSmtLibSolver}.
     */
    @Override
    public boolean supportsAllSat() {
        return false;
    }

    /**
     * Issues MathSAT's {@code (check-allsat (...))} extension and collects one {@link Valuation}
     * per model.
     *
     * <p>The reply is a sequence of parenthesised blocks, one per model, terminated by a bare
     * status token:
     *
     * <pre>
     *   ( (p1 false) (p2 false) )
     *   ( (p1 true)  (p2 true)  )
     *   sat
     * </pre>
     *
     * <p>Each block arrives as its own {@code readResponse()} and the loop simply stops at the
     * status token. This is the only place where several parenthesised responses arrive in a row,
     * so it is the only caller that depends on the response reader skipping the whitespace between
     * them -- see {@code GenericSmtLibSolverBinary.ReadProcessor}, where getting that wrong
     * delivered every block after the first one line at a time. The blocks are parsed directly
     * rather than through the general response grammar, which models {@code get-model} output
     * ({@code define-fun} forms) and does not describe this shape.
     */
    @Override
    public Collection<? extends Valuation> allSat(
            final List<? extends ConstDecl<BoolType>> important) {
        if (!supportsAllSat()) {
            throw new UnsupportedOperationException(
                    "This solver does not support all-sat; check supportsAllSat() first");
        }
        if (important.isEmpty()) {
            // No variables to enumerate over: the answer is one empty model iff satisfiable.
            return check().isSat() ? List.of(ImmutableValuation.builder().build()) : List.of();
        }

        final var symbols =
                important.stream().map(symbolTable::getSymbol).collect(Collectors.joining(" "));
        solverBinary.issueCommand("(check-allsat (" + symbols + "))");

        final List<Valuation> models = new ArrayList<>();
        while (true) {
            final String response = solverBinary.readResponse().trim();
            if (response.isEmpty()) {
                continue;
            }
            if (!response.startsWith("(")) {
                // status token closes the enumeration
                if (response.startsWith("unsat")) {
                    status = SolverStatus.UNSAT;
                } else if (response.startsWith("sat")) {
                    status = SolverStatus.SAT;
                } else {
                    throw new UnknownSolverStatusException();
                }
                break;
            }
            if (response.startsWith("(error")) {
                throw new SmtLibSolverException(response);
            }
            models.add(parseAllSatModel(response));
        }
        return models;
    }

    /** Parses one {@code ( (sym value) ... )} block into a {@link Valuation}. */
    private Valuation parseAllSatModel(final String block) {
        final var builder = ImmutableValuation.builder();
        final var matcher = ALLSAT_ASSIGNMENT.matcher(block);
        while (matcher.find()) {
            final String symbol = matcher.group(1);
            final boolean value = Boolean.parseBoolean(matcher.group(2));
            if (!symbolTable.definesSymbol(symbol)) {
                continue; // not one of ours; MathSAT may name auxiliary literals
            }
            final ConstDecl<?> decl = symbolTable.getConst(symbol);
            if (decl.getType() instanceof BoolType) {
                @SuppressWarnings("unchecked")
                final ConstDecl<BoolType> boolDecl = (ConstDecl<BoolType>) decl;
                builder.put(boolDecl, value ? BoolExprs.True() : BoolExprs.False());
            }
        }
        return builder.build();
    }

    private static final Pattern ALLSAT_ASSIGNMENT =
            Pattern.compile("\\(\\s*([^()\\s]+)\\s+(true|false)\\s*\\)");

    @Override
    public SolverStatus check() {
        solverBinary.issueCommand("(check-sat)");

        final String rp = solverBinary.readResponse();
        final var res = parseResponse(rp);
        if (res.isError()) {
            throw new SmtLibSolverException(res.getReason());
        }
        if (!res.isSpecific()) {
            throw new AssertionError();
        }
        final CheckSatResponse checkSatResponse = res.asSpecific().asCheckSatResponse();
        if (checkSatResponse.isSat()) {
            status = SolverStatus.SAT;
            return status;
        }
        if (checkSatResponse.isUnsat()) {
            status = SolverStatus.UNSAT;
            return status;
        }
        throw new UnknownSolverStatusException();
    }

    @Override
    public void push() {
        assertions.push();
        declarationStack.push();
        typeStack.push();
        issueGeneralCommand("(push 1)");
    }

    @Override
    public void pop(int n) {
        assertions.pop(n);
        declarationStack.pop(n);
        typeStack.pop(n);
        issueGeneralCommand("(pop 1)");
        clearState();
    }

    @Override
    public void reset() {
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
    public Collection<Expr<BoolType>> getUnsatCore() {
        checkState(status == SolverStatus.UNSAT, "Cannot get unsat core if status is not UNSAT");

        if (unsatCore == null) {
            unsatCore = extractUnsatCore();
        }

        return Collections.unmodifiableCollection(unsatCore);
    }

    private Collection<Expr<BoolType>> extractUnsatCore() {
        assert status == SolverStatus.UNSAT;
        assert unsatCore == null;

        final Collection<Expr<BoolType>> unsatCore = new LinkedList<>();
        final Collection<String> unsatCoreLabels;

        solverBinary.issueCommand("(get-unsat-core)");
        final var res = parseResponse(solverBinary.readResponse());
        if (res.isError()) {
            throw new SmtLibSolverException(res.getReason());
        } else if (res.isSpecific()) {
            final GetUnsatCoreResponse getUnsatCoreResponse =
                    res.asSpecific().asGetUnsatCoreResponse();
            unsatCoreLabels = getUnsatCoreResponse.getLabels();
        } else {
            throw new AssertionError();
        }

        for (final var label : unsatCoreLabels) {
            final Expr<BoolType> assumption = assumptions.get(label);
            assert assumption != null;
            unsatCore.add(assumption);
        }

        return unsatCore;
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return assertions.toCollection();
    }

    @Override
    public void close() throws Exception {
        solverBinary.close();
    }

    private void init() {
        issueGeneralCommand("(set-option :print-success true)");
        issueGeneralCommand("(set-option :produce-models true)");
        if (unsatCoreEnabled) {
            issueGeneralCommand("(set-option :produce-unsat-cores true)");
        }
        if (logic.equals("HORN")) {
            issueGeneralCommand("(set-option :produce-proofs true)");
        }
        issueGeneralCommand("(set-logic " + logic + ")");
    }

    protected void clearState() {
        status = null;
        model = null;
        unsatCore = null;
    }

    protected void issueGeneralCommand(String command) {
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
