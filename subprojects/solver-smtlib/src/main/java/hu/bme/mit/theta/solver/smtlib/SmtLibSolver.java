package hu.bme.mit.theta.solver.smtlib;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.UnknownSolverStatusException;
import hu.bme.mit.theta.solver.impl.StackImpl;
import hu.bme.mit.theta.solver.smtlib.binary.ContinousSolverBinary;
import hu.bme.mit.theta.solver.smtlib.binary.SolverBinary;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.parser.CheckSatResponse;
import hu.bme.mit.theta.solver.smtlib.parser.GeneralResponse;
import hu.bme.mit.theta.solver.smtlib.parser.GetModelResponse;
import hu.bme.mit.theta.solver.smtlib.parser.GetUnsatCoreResponse;
import hu.bme.mit.theta.solver.smtlib.parser.ThrowExceptionErrorListener;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class SmtLibSolver implements Solver {
    private final SolverBinary solverBinary;

    private final SmtLibSymbolTable symbolTable;
    private final SmtLibTransformationManager transformationManager;
    private final SmtLibTermTransformer termTransformer;

    private final Stack<Expr<BoolType>> assertions;
    private final Map<String, Expr<BoolType>> assumptions;
    private final Set<ConstDecl<?>> declarations;
    private final Stack<Set<ConstDecl<?>>> declarationStack;

    private static final String ASSUMPTION_LABEL = "_LABEL_%d";
    private int labelNum = 0;

    private Valuation model;
    private Collection<Expr<BoolType>> unsatCore;
    private SolverStatus status;

    public SmtLibSolver(
        final SmtLibSymbolTable symbolTable, final SmtLibTransformationManager transformationManager,
        final SmtLibTermTransformer termTransformer, final Path solverPath, final String[] args
    ) {
        this.solverBinary = new ContinousSolverBinary(solverPath, args);

        this.symbolTable = symbolTable;
        this.transformationManager = transformationManager;
        this.termTransformer = termTransformer;

        assertions = new StackImpl<>();
        assumptions = new HashMap<>();
        declarations = new HashSet<>();
        declarationStack = new StackImpl<>();

        init();
    }

    @Override
    public void add(Expr<BoolType> assertion) {
        final var consts = ExprUtils.getConstants(assertion);
        consts.removeAll(declarations);
        declarations.addAll(consts);
        declarationStack.add(consts);

        final var term = transformationManager.toTerm(assertion);

        consts.stream().map(symbolTable::getDeclaration).forEach(this::issueGeneralCommand);
        issueGeneralCommand(String.format("(assert %s)%n", term));

        clearState();
    }

    @Override
    public void track(Expr<BoolType> assertion) {
        final var consts = ExprUtils.getConstants(assertion);
        consts.removeAll(declarations);
        declarations.addAll(consts);
        declarationStack.add(consts);

        final var term = transformationManager.toTerm(assertion);
        final var label = String.format(ASSUMPTION_LABEL, labelNum++);
        assumptions.put(label, assertion);

        consts.stream().map(symbolTable::getDeclaration).forEach(this::issueGeneralCommand);
        issueGeneralCommand(String.format("(assert (! %s :named %s))%n", term, label));

        clearState();
    }

    @Override
    public SolverStatus check() {
        var res = parseResponse(solverBinary.issueCommand("(check-sat)"));
        if(res.isError()) {
            throw new SmtLibSolverException(res.getReason());
        }
        else if(res.isSpecific()) {
            final CheckSatResponse checkSatResponse = res.asSpecific();
            if(checkSatResponse.isSat()) {
                status = SolverStatus.SAT;
            }
            else if(checkSatResponse.isUnsat()) {
                status = SolverStatus.UNSAT;
            }
            else {
                throw new UnknownSolverStatusException();
            }
        }
        else {
            throw new AssertionError();
        }

        return status;
    }

    @Override
    public void push() {
        assertions.push();
        declarationStack.push();
        declarations.clear();
        declarations.addAll(declarationStack.toCollection().stream().flatMap(Collection::stream).collect(Collectors.toSet()));
        issueGeneralCommand("(push)");
    }

    @Override
    public void pop(int n) {
        assertions.pop(n);
        declarationStack.pop(n);
        issueGeneralCommand("(pop)");
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

        final var res = parseResponse(solverBinary.issueCommand("(get-model)"));
        if(res.isError()) {
            throw new SmtLibSolverException(res.getReason());
        }
        else if(res.isSpecific()) {
            final GetModelResponse getModelResponse = res.asSpecific();
            return new SmtLibValuation(getModelResponse);
        }
        else {
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

        final var res = parseResponse(solverBinary.issueCommand("(get-unsat-core)"));
        if(res.isError()) {
            throw new SmtLibSolverException(res.getReason());
        }
        else if(res.isSpecific()) {
            final GetUnsatCoreResponse getUnsatCoreResponse = res.asSpecific();
            unsatCoreLabels = getUnsatCoreResponse.getLabels();
        }
        else {
            throw new AssertionError();
        }

        for(final var label : unsatCoreLabels) {
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

    protected void init() {
        issueGeneralCommand("(set-option :print-success true)");
        issueGeneralCommand("(set-option :produce-models true)");
        issueGeneralCommand("(set-option :produce-unsat-cores true)");
        issueGeneralCommand("(set-logic ALL)");
    }

    private void clearState() {
        status = null;
        model = null;
        unsatCore = null;
    }

    private void issueGeneralCommand(String command) {
        var res = parseResponse(solverBinary.issueCommand(command));
        if(res.isError()) {
            throw new SmtLibSolverException(res.getReason());
        }
    }

    private GeneralResponse parseResponse(final String response) {
        try {
            final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(response));
            final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
            lexer.removeErrorListeners();
            lexer.addErrorListener(new ThrowExceptionErrorListener());
            parser.removeErrorListeners();
            parser.addErrorListener(new ThrowExceptionErrorListener());
            return GeneralResponse.fromContext(parser.response());
        }
        catch (Exception e) {
            throw new SmtLibSolverException("Could not parse solver output: " + response, e);
        }
    }

    private final class SmtLibValuation extends Valuation {
        private final GetModelResponse model;
        private final Map<Decl<?>, LitExpr<?>> constToExpr;
        private volatile Collection<ConstDecl<?>> constDecls = null;

        public SmtLibValuation(final GetModelResponse model) {
            this.model = model;
            constToExpr = new HashMap<>();
        }

        @Override
        public Collection<? extends Decl<?>> getDecls() {
            Collection<ConstDecl<?>> result = constDecls;
            if (result == null) {
                result = constDeclsOf(model);
                constDecls = result;
            }
            return result;
        }

        @Override
        public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(Decl<DeclType> decl) {
            checkNotNull(decl);

            if (!(decl instanceof ConstDecl)) {
                return Optional.empty();
            }

            final ConstDecl<DeclType> constDecl = (ConstDecl<DeclType>) decl;

            LitExpr<?> val = constToExpr.get(constDecl);
            if (val == null) {
                val = extractLiteral(constDecl);
                if (val != null) {
                    constToExpr.put(constDecl, val);
                }
            }

            @SuppressWarnings("unchecked") final LitExpr<DeclType> tVal = (LitExpr<DeclType>) val;
            return Optional.ofNullable(tVal);
        }

        private <DeclType extends Type> LitExpr<?> extractLiteral(final ConstDecl<DeclType> decl) {
            final String symbol = transformationManager.toSymbol(decl);
            final Type type = decl.getType();
            /*if (type instanceof FuncType) {
                return extractFuncLiteral(funcDecl);
            } else if (type instanceof ArrayType) {
                return extractArrayLiteral(funcDecl);
            } else if (type instanceof BvType) {
                return extractBvConstLiteral(funcDecl, (BvType) type);
            } else {*/
            //}
            if(type instanceof ArrayType) {
                return extractArrayLiteral(symbol, (ArrayType<?, ?>) type);
            }
            else if (type instanceof BvType) {
                return extractBvConstLiteral(symbol, (BvType) type);
            }
            else {
                return extractConstLiteral(symbol, type);
            }
        }

        private LitExpr<?> extractArrayLiteral(final String symbol, final ArrayType<?, ?> type) {
            final String term = model.getTerm(symbol);
            if (term == null) {
                return null;
            } else {
                return (LitExpr<?>) ExprUtils.simplify(cast(termTransformer.toArrayLitExpr(term, type, model), type));
            }
        }

        private LitExpr<?> extractBvConstLiteral(final String symbol, final BvType type) {
            final String term = model.getTerm(symbol);
            if (term == null) {
                return null;
            } else {
                BvLitExpr expr = (BvLitExpr) termTransformer.toExpr(term, model);
                return Bv(expr.getValue(), type.isSigned());
            }
        }

        private LitExpr<?> extractConstLiteral(final String symbol, final Type type) {
            final String term = model.getTerm(symbol);
            if (term == null) {
                return null;
            } else {
                return (LitExpr<?>) ExprUtils.simplify(cast(termTransformer.toExpr(term, model), type));
            }
        }

        @Override
        public Map<Decl<?>, LitExpr<?>> toMap() {
            getDecls().forEach(this::eval);
            return Collections.unmodifiableMap(constToExpr);
        }

        private Collection<ConstDecl<?>> constDeclsOf(final GetModelResponse model) {
            final ImmutableList.Builder<ConstDecl<?>> builder = ImmutableList.builder();
            for (final var symbol : model.getDecls()) {
                if (symbolTable.definesSymbol(symbol)) {
                    final ConstDecl<?> constDecl = symbolTable.getConst(symbol);
                    builder.add(constDecl);
                }
            }
            return builder.build();
        }
    }

}
