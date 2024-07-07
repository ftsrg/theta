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
package hu.bme.mit.theta.solver.z3;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_decl_kind;
import hu.bme.mit.theta.common.container.Containers;
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
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.solver.HornSolver;
import hu.bme.mit.theta.solver.ProofNode;
import hu.bme.mit.theta.solver.ProofNode.Builder;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.*;
import hu.bme.mit.theta.solver.impl.StackImpl;

import java.util.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

final class Z3Solver implements UCSolver, Solver, HornSolver {

    private final Z3SymbolTable symbolTable;
    private final Z3TransformationManager transformationManager;
    private final Z3TermTransformer termTransformer;

    private final com.microsoft.z3.Context z3Context;
    private final com.microsoft.z3.Solver z3Solver;

    private final Stack<Expr<BoolType>> assertions;
    private final Map<String, Expr<BoolType>> assumptions;

    private static final String ASSUMPTION_LABEL = "_LABEL_%d";
    private int labelNum = 0;

    private Valuation model;
    private Collection<Expr<BoolType>> unsatCore;
    private SolverStatus status;

    public Z3Solver(final Z3SymbolTable symbolTable,
                    final Z3TransformationManager transformationManager,
                    final Z3TermTransformer termTransformer, final com.microsoft.z3.Context z3Context,
                    final com.microsoft.z3.Solver z3Solver) {
        this.symbolTable = symbolTable;
        this.transformationManager = transformationManager;
        this.termTransformer = termTransformer;
        this.z3Context = z3Context;
        this.z3Solver = z3Solver;

        assertions = new StackImpl<>();
        assumptions = Containers.createMap();
    }

    ////

    @Override
    public void add(final Expr<BoolType> assertion) {
        checkNotNull(assertion);
        final com.microsoft.z3.BoolExpr term = (com.microsoft.z3.BoolExpr) transformationManager.toTerm(
                assertion);
        add(assertion, term);
    }

    void add(final Expr<BoolType> assertion, final com.microsoft.z3.BoolExpr term) {
        assertions.add(assertion);
        z3Solver.add(term);
        clearState();
    }

    @Override
    public void track(final Expr<BoolType> assertion) {
        checkNotNull(assertion);

        assertions.add(assertion);
        final com.microsoft.z3.BoolExpr term = (com.microsoft.z3.BoolExpr) transformationManager.toTerm(
                assertion);
        final String label = String.format(ASSUMPTION_LABEL, labelNum++);
        final com.microsoft.z3.BoolExpr labelTerm = z3Context.mkBoolConst(label);

        assumptions.put(label, assertion);

        z3Solver.assertAndTrack(term, labelTerm);

        clearState();
    }

    @Override
    public SolverStatus check() {
        final Status z3Status = z3Solver.check();
        status = transformStatus(z3Status);
        return status;
    }

    private SolverStatus transformStatus(final Status z3Status) {
        switch (z3Status) {
            case SATISFIABLE:
                return SolverStatus.SAT;
            case UNSATISFIABLE:
                return SolverStatus.UNSAT;
            default:
                throw new UnknownSolverStatusException();
        }
    }

    @Override
    public void push() {
        assertions.push();
        z3Solver.push();
    }

    @Override
    public void pop(final int n) {
        assertions.pop(n);
        z3Solver.pop(n);
        clearState();
    }

    @Override
    public void reset() {
        z3Solver.reset();
        assertions.clear();
        assumptions.clear();
        symbolTable.clear();
        transformationManager.reset();
        clearState();
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

        assert model != null;
        return model;
    }

    private Valuation extractModel() {
        assert status == SolverStatus.SAT;
        assert model == null;

        final com.microsoft.z3.Model z3Model = z3Solver.getModel();
        assert z3Model != null;

        return new Z3Model(z3Model);
    }

    @Override
    public Collection<Expr<BoolType>> getUnsatCore() {
        checkState(status == SolverStatus.UNSAT, "Cannot get unsat core if status is not UNSAT");

        if (unsatCore == null) {
            unsatCore = extractUnsatCore();
        }

        assert unsatCore != null;
        return Collections.unmodifiableCollection(unsatCore);
    }

    private Collection<Expr<BoolType>> extractUnsatCore() {
        assert status == SolverStatus.UNSAT;
        assert unsatCore == null;

        final Collection<Expr<BoolType>> unsatCore = new LinkedList<>();

        final com.microsoft.z3.Expr[] z3UnsatCore = z3Solver.getUnsatCore();

        for (int i = 0; i < z3UnsatCore.length; i = i + 1) {
            final com.microsoft.z3.Expr term = z3UnsatCore[i];

            checkState(term.isConst(), "Term is not constant.");

            final String label = term.toString();
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

    private void clearState() {
        status = null;
        model = null;
        unsatCore = null;
    }

    @Override
    public void close() {
        z3Context.interrupt();
    }

    private <T1 extends Type, T2 extends Type> Expr<?> funcApp(Expr<?> func, Expr<?> param) {
        final Expr<FuncType<T1, T2>> funcTyped = (Expr<FuncType<T1, T2>>) func;
        final Expr<T1> paramTyped = (Expr<T1>) param;
        return App(funcTyped, paramTyped);
    }

    private Expr<BoolType> toProofExpr(com.microsoft.z3.Expr<?> expr) {
        final var args = expr.getArgs();
        final var lastArg = args[args.length - 1];
        checkState(lastArg.isApp());
        final var name = lastArg.getFuncDecl().getName().toString();
        final var params = lastArg.getArgs();
        final var paramValues = Arrays.stream(params).map(termTransformer::toExpr).toList();
        final List<Type> paramTypes = paramValues.stream().map(expr1 -> (Type) expr1.getType()).toList();

        final var funcType = paramTypes.stream().reduce(Bool(), (res, param) -> FuncType.of(param, res));
        final var decl = Const(name, funcType);
        Expr<?> func = decl.getRef();
        for (Expr<?> paramValue : paramValues) {
            func = funcApp(func, paramValue);
        }
        return (Expr<BoolType>) func;
    }

    /**
     * This is a best-effort solution, hopefully would support (most) CHCs at least.
     * Taken from https://github.com/ethereum/solidity/blob/5917fd82b3ca4cab5f817f78b8da8ebe409dd02e/libsmtutil/Z3CHCInterface.cpp#L130
     * and adapted to the Java API.
     */
    @Override
    public ProofNode getProof() {
        checkState(status == SolverStatus.UNSAT, "Cannot get proof if status is not UNSAT");
        com.microsoft.z3.Expr<?> proof = z3Solver.getProof();

        Deque<com.microsoft.z3.Expr<?>> proofStack = new LinkedList<>();
        proofStack.push(proof.getArgs()[0]);

        Expr<BoolType> root = cast(False(), Bool());
        final var rootBuilder = new ProofNode.Builder(root);

        Map<Integer, ProofNode.Builder> visited = new LinkedHashMap<>();
        visited.put(proofStack.peek().getId(), rootBuilder);

        while (!proofStack.isEmpty()) {
            final var proofNodeExpr = proofStack.pop();
            if (!visited.containsKey(proofNodeExpr.getId())) {
                throw new Z3Exception("Node should exist in the graph nodes");
            }
            final var proofNode = visited.get(proofNodeExpr.getId());

            if (proofNodeExpr.isApp() && proofNodeExpr.getFuncDecl().getDeclKind() == Z3_decl_kind.Z3_OP_PR_HYPER_RESOLVE) {
                if (proofNodeExpr.getArgs().length > 0) {
                    for (int i = 1; i < proofNodeExpr.getArgs().length - 1; ++i) {
                        final var child = proofNodeExpr.getArgs()[i];
                        if (!visited.containsKey(child.getId())) {
                            visited.put(child.getId(), new Builder(toProofExpr(child)));
                            proofStack.push(child);
                        }
                        proofNode.addChild(visited.get(child.getId()));
                    }
                }
            }
        }


        return rootBuilder.build();
    }

    ////

    private final class Z3Model extends Valuation {

        private final com.microsoft.z3.Model z3Model;
        private final Map<Decl<?>, LitExpr<?>> constToExpr;
        private volatile Collection<ConstDecl<?>> constDecls = null;

        public Z3Model(final com.microsoft.z3.Model z3Model) {
            this.z3Model = z3Model;
            constToExpr = Containers.createMap();
        }

        @Override
        public Collection<ConstDecl<?>> getDecls() {
            Collection<ConstDecl<?>> result = constDecls;
            if (result == null) {
                result = constDeclsOf(z3Model);
                constDecls = result;
            }
            return result;
        }

        @Override
        public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
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
            final FuncDecl funcDecl = transformationManager.toSymbol(decl);
            final Type type = decl.getType();
            if (type instanceof FuncType) {
                return extractFuncLiteral(funcDecl);
            } else if (type instanceof ArrayType) {
                return extractArrayLiteral(funcDecl);
            } else if (type instanceof BvType) {
                return extractBvConstLiteral(funcDecl);
            } else if (type instanceof EnumType) {
                return extractEnumLiteral(decl, funcDecl);
            } else {
                return extractConstLiteral(funcDecl);
            }
        }

        private LitExpr<?> extractFuncLiteral(final FuncDecl funcDecl) {
            final Expr<?> expr = termTransformer.toFuncLitExpr(funcDecl, z3Model,
                    new ArrayList<>());
            return (LitExpr<?>) expr;
        }

        private LitExpr<?> extractArrayLiteral(final FuncDecl funcDecl) {
            final Expr<?> expr = termTransformer.toArrayLitExpr(funcDecl, z3Model,
                    new ArrayList<>());
            return (LitExpr<?>) expr;
        }

        private LitExpr<?> extractBvConstLiteral(final FuncDecl funcDecl) {
            final com.microsoft.z3.Expr term = z3Model.getConstInterp(funcDecl);
            if (term == null) {
                return null;
            } else {
                return (BvLitExpr) termTransformer.toExpr(term);
            }
        }

        private LitExpr<?> extractEnumLiteral(final ConstDecl<?> constDecl, final FuncDecl funcDecl) {
            return EnumLitExpr.of((EnumType) constDecl.getType(), z3Model.getConstInterp(funcDecl).toString());
        }

        private LitExpr<?> extractConstLiteral(final FuncDecl funcDecl) {
            final com.microsoft.z3.Expr term = z3Model.getConstInterp(funcDecl);
            if (term == null) {
                return null;
            } else {
                return (LitExpr<?>) termTransformer.toExpr(term);
            }
        }

        @Override
        public Map<Decl<?>, LitExpr<?>> toMap() {
            getDecls().forEach(this::eval);
            return Collections.unmodifiableMap(constToExpr);
        }

        ////

        private Collection<ConstDecl<?>> constDeclsOf(final com.microsoft.z3.Model z3Model) {
            final ImmutableList.Builder<ConstDecl<?>> builder = ImmutableList.builder();
            for (final FuncDecl symbol : z3Model.getDecls()) {
                if (symbolTable.definesSymbol(symbol)) {
                    final ConstDecl<?> constDecl = symbolTable.getConst(symbol);
                    builder.add(constDecl);
                }
                /* else {
                    if (!assumptions.containsKey(symbol.getName().toString())) {
                        // Quantifier?
                    }
                } */
            }
            return builder.build();
        }
    }

}
