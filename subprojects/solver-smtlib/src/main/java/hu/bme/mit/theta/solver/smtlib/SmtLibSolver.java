package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
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
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.nio.file.Path;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;

public class SmtLibSolver implements Solver {
    private final SolverBinary solverBinary;

    private final SmtLibSymbolTable symbolTable;
    private final SmtLibTransformationManager transformationManager;

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
        final Path solverPath, final String[] args
    ) {
        this.solverBinary = new ContinousSolverBinary(solverPath, args);

        this.symbolTable = symbolTable;
        this.transformationManager = transformationManager;

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
                return SolverStatus.SAT;
            }
            else if(checkSatResponse.isUnsat()) {
                return SolverStatus.UNSAT;
            }
            else {
                throw new UnknownSolverStatusException();
            }
        }
        else {
            throw new AssertionError();
        }
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
            //model = extractModel();
        }

        assert model != null;
        return model;
    }

    @Override
    public Collection<Expr<BoolType>> getUnsatCore() {
        checkState(status == SolverStatus.UNSAT, "Cannot get unsat core if status is not UNSAT");

        if (unsatCore == null) {
            //unsatCore = extractUnsatCore();
        }

        assert unsatCore != null;
        return Collections.unmodifiableCollection(unsatCore);
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
            return GeneralResponse.fromContext(parser.response());
        }
        catch (Exception e) {
            throw new SmtLibSolverException("Could not parse solver output: " + response, e);
        }
    }

}
