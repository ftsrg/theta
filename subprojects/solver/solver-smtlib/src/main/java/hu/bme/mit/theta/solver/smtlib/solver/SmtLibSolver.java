/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

import com.microsoft.z3.Z3Exception;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.HornSolver;
import hu.bme.mit.theta.solver.ProofNode;
import hu.bme.mit.theta.solver.ProofNode.Builder;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.*;
import hu.bme.mit.theta.solver.impl.StackImpl;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.SortContext;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibValuation;
import hu.bme.mit.theta.solver.smtlib.solver.parser.*;
import hu.bme.mit.theta.solver.smtlib.solver.parser.CheckSatResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GeneralResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GetModelResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GetProofResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GetUnsatCoreResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.ThrowExceptionErrorListener;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.util.*;
import java.util.stream.Collectors;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.ExprUtils.extractFuncAndArgs;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class SmtLibSolver implements UCSolver, Solver, HornSolver {

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
    private final boolean unsatCoreEnabled;
    private int labelNum = 0;

    protected Valuation model;
    protected Collection<Expr<BoolType>> unsatCore;
    protected SolverStatus status;

    public SmtLibSolver(
            final SmtLibSymbolTable symbolTable,
            final SmtLibTransformationManager transformationManager,
            final SmtLibTermTransformer termTransformer, final SmtLibSolverBinary solverBinary,
            boolean unsatCoreEnabled
    ) {
        this(symbolTable, transformationManager, termTransformer, solverBinary, unsatCoreEnabled, SmtLibEnumStrategy.getDefaultStrategy(), "ALL");
    }

    public SmtLibSolver(
            final SmtLibSymbolTable symbolTable,
            final SmtLibTransformationManager transformationManager,
            final SmtLibTermTransformer termTransformer, final SmtLibSolverBinary solverBinary,
            boolean unsatCoreEnabled,
            final SmtLibEnumStrategy enumStrategy,
            final String logic
    ) {
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
        final var consts = ExprUtils.getConstants(assertion);
        consts.removeAll(declarationStack.toCollection());
        declarationStack.add(consts);

        assertions.add(assertion);
        enumStrategy.declareDatatypes((Collection<Type>) consts.stream().map(ConstDecl::getType).toList(), typeStack, this::issueGeneralCommand);
        consts.stream().map(symbolTable::getDeclaration).forEach(this::issueGeneralCommand);
        issueGeneralCommand(String.format("(assert %s)", enumStrategy.wrapAssertionExpression(term, ExprUtils.getConstants(assertion).stream().collect(Collectors.toMap(c -> c, symbolTable::getSymbol)))));

        clearState();
    }

    @Override
    public void track(Expr<BoolType> assertion) {
        final var consts = ExprUtils.getConstants(assertion);
        consts.removeAll(declarationStack.toCollection());
        declarationStack.add(consts);

        final var term = transformationManager.toTerm(assertion);
        final var label = String.format(ASSUMPTION_LABEL, labelNum++);
        assumptions.put(label, assertion);
        assertions.add(assertion);

        consts.stream().map(symbolTable::getDeclaration).forEach(this::issueGeneralCommand);
        enumStrategy.declareDatatypes((Collection<Type>) consts.stream().map(ConstDecl::getType).toList(), typeStack, this::issueGeneralCommand);
        issueGeneralCommand(String.format("(assert (! %s :named %s))", enumStrategy.wrapAssertionExpression(term, ExprUtils.getConstants(assertion).stream().collect(Collectors.toMap(c -> c, symbolTable::getSymbol))), label));

        clearState();
    }

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
            return new SmtLibValuation(symbolTable, transformationManager, termTransformer,
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
            final GetUnsatCoreResponse getUnsatCoreResponse = res.asSpecific()
                    .asGetUnsatCoreResponse();
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


    public static Type transformSort(final SortContext ctx) {
        final String name = ctx.identifier().symbol().getText();
        return switch (name) {
            case "Int" -> Int();
            case "Bool" -> Bool();
            case "Real" -> Rat();
            case "BitVec" -> {
                assert ctx.identifier().index().size() == 1;
                yield BvExprs.BvType(Integer.parseInt(ctx.identifier().index().get(0).getText()));
            }
            case "Array" -> {
                assert ctx.sort().size() == 2;
                yield Array(transformSort(ctx.sort().get(0)), transformSort(ctx.sort().get(1)));
            }
            default -> throw new UnsupportedOperationException();
        };
    }

    @Override
    public ProofNode getProof() {
        solverBinary.issueCommand("(get-proof)");
        var response = solverBinary.readResponse();
        final var res = parseResponse(response);
        if (res.isError()) {
            throw new SmtLibSolverException(res.getReason());
        } else if (res.isSpecific()) {
            final GetProofResponse getModelResponse = res.asSpecific().asGetProofResponse();
            getModelResponse.getFunDeclarations().forEach((name, def) -> {
                var type = transformSort(def.get2());
                for (SortContext s : def.get1()) {
                    type = FuncType.of(transformSort(s), type);
                }
                symbolTable.put(Const(name, type), name, def.get3());
            });
            final var proof = termTransformer.toExpr(getModelResponse.getProof(), Bool(), new SmtLibModel(Collections.emptyMap()));
            return proofFromExpr(proof);
        } else {
            throw new AssertionError();
        }
    }

    private ProofNode proofFromExpr(Expr<BoolType> proof) {
        checkState(proof instanceof FuncAppExpr<?, ?>, "Proof must be a function application.");
        int id = 0;
        final Map<Expr<?>, Integer> lookup = new LinkedHashMap<>();

        final var args = extractFuncAndArgs((FuncAppExpr<?, ?>) proof).get2();

        Deque<Expr<?>> proofStack = new LinkedList<>();
        proofStack.push(args.get(0));
        lookup.put(args.get(0), id++);

        Expr<BoolType> root = cast(False(), Bool());
        final var rootBuilder = new ProofNode.Builder(root);

        Map<Integer, ProofNode.Builder> visited = new LinkedHashMap<>();
        visited.put(lookup.get(args.get(0)), rootBuilder);

        while (!proofStack.isEmpty()) {
            final var proofNodeExpr = proofStack.pop();
            if (!visited.containsKey(lookup.getOrDefault(proofNodeExpr, -1))) {
                throw new Z3Exception("Node should exist in the graph nodes");
            }
            final var proofNode = visited.get(lookup.get(proofNodeExpr));

            if (proofNodeExpr instanceof FuncAppExpr<?, ?> funcAppExpr) {
                final var nameAndArgs = extractFuncAndArgs(funcAppExpr);
                if (nameAndArgs.get1() instanceof RefExpr<?> refName && refName.getDecl().getName().startsWith("hyper-res")) {
                    if (!nameAndArgs.get2().isEmpty()) {
                        for (int i = 1; i < nameAndArgs.get2().size() - 1; ++i) {
                            final var child = nameAndArgs.get2().get(i);
                            if (!visited.containsKey(lookup.getOrDefault(child, -1))) {
                                if (!lookup.containsKey(child)) {
                                    lookup.put(child, id++);
                                }
                                visited.put(lookup.get(child), new Builder(extractProofExpr(child)));
                                proofStack.push(child);
                            }
                            proofNode.addChild(visited.get(lookup.get(child)));
                        }
                    }
                }
            }
        }
        return rootBuilder.build();
    }

    private Expr<BoolType> extractProofExpr(Expr<?> expr) {
        checkState(expr instanceof FuncAppExpr<?, ?>, "Proof should be function application.");
        final var nameAndArgs = extractFuncAndArgs((FuncAppExpr<?, ?>) expr);
        final var args = nameAndArgs.get2();
        final var lastArg = args.get(args.size() - 1);
        checkState(lastArg instanceof FuncAppExpr<?, ?>, "Proof should be function application.");
        return (Expr<BoolType>) lastArg;
    }
}
