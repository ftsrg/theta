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

import static com.google.common.base.Preconditions.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.microsoft.z3.*;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.solver.*;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;
import java.util.*;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.Map;
import java.util.Optional;
import java.util.stream.IntStream;

class Z3Solver implements UCSolver, Solver, ItpSolver {

    protected final Z3SymbolTable symbolTable;
    protected final Z3TransformationManager transformationManager;
    protected final Z3TermTransformer termTransformer;

    protected final Context z3Context;
    protected final com.microsoft.z3.Solver z3Solver;

    private final Stack<Expr<BoolType>> assertions;
    private final Stack<Z3ItpMarker> markers;
    private final Map<String, Expr<BoolType>> assumptions;

    private static final String ASSUMPTION_LABEL = "_LABEL_%d";
    private int labelNum = 0;

    protected Valuation model;
    protected Collection<Expr<BoolType>> unsatCore;
    protected SolverStatus status;

    public Z3Solver(
            final Z3SymbolTable symbolTable,
            final Z3TransformationManager transformationManager,
            final Z3TermTransformer termTransformer,
            final Context z3Context,
            final com.microsoft.z3.Solver z3Solver) {
        this.symbolTable = symbolTable;
        this.transformationManager = transformationManager;
        this.termTransformer = termTransformer;
        this.z3Context = z3Context;
        this.z3Solver = z3Solver;

        assertions = new StackImpl<>();
        assumptions = Containers.createMap();
        markers = new StackImpl<>();
    }

    ////

    @Override
    public void add(final Expr<BoolType> assertion) {
        checkNotNull(assertion);
        final BoolExpr term = (BoolExpr) transformationManager.toTerm(assertion);
        add(assertion, term);
    }

    void add(final Expr<BoolType> assertion, final BoolExpr term) {
        assertions.add(assertion);
        z3Solver.add(term);
        clearState();
    }

    @Override
    public void track(final Expr<BoolType> assertion) {
        checkNotNull(assertion);

        assertions.add(assertion);
        final BoolExpr term = (BoolExpr) transformationManager.toTerm(assertion);
        final String label = String.format(ASSUMPTION_LABEL, labelNum++);
        final BoolExpr labelTerm = z3Context.mkBoolConst(label);

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
        markers.push();
        z3Solver.push();
    }

    @Override
    public void pop(final int n) {
        assertions.pop(n);
        markers.pop(n);
        z3Solver.pop(n);
        clearState();
    }

    @Override
    public void reset() {
        z3Solver.reset();
        assertions.clear();
        markers.clear();
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

        final Model z3Model = z3Solver.getModel();
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

    @Override
    public ImmutableMap<String, String> getStatistics() {
        Statistics stats = z3Solver.getStatistics();
        ImmutableMap.Builder<String, String> builder = ImmutableMap.builder();
        Set<String> keys = new HashSet<>();
        for (String key : stats.getKeys()) {
            if (keys.contains(key)) continue;
            builder.put(key, stats.get(key).getValueString());
            keys.add(key);
        }
        return builder.buildOrThrow();
    }

    @Override
    public Expr<BoolType> simplify(Expr<BoolType> expr) {
        try {
            Tactic t =
                    z3Context.then(
                            z3Context.mkTactic(
                                    "simplify"), // Always start with basic simplification
                            z3Context.mkTactic("propagate-values"), // Propagate known constants
                            z3Context.mkTactic("ctx-simplify"), // Contextual simplification
                            z3Context.mkTactic(
                                    "ctx-solver-simplify") // Uses solver context for even more
                            // simplification
                            );
            Goal g = z3Context.mkGoal(true, false, false);
            g.add(transformationManager.toTerm(expr));
            ApplyResult ar = t.apply(g);
            BoolExpr result = ar.getSubgoals()[0].AsBoolExpr();
            return (Expr<BoolType>) termTransformer.toExpr(result);
        } catch (Throwable t) {
            return expr;
        }
    }

    @Override
    public ItpPattern createTreePattern(ItpMarkerTree<? extends ItpMarker> root) {
        checkNotNull(root);
        return Z3ItpPattern.of(root);
    }

    @Override
    public ItpMarker createMarker() {
        final Z3ItpMarker marker = new Z3ItpMarker();
        markers.add(marker);
        return marker;
    }

    @Override
    public void add(ItpMarker marker, Expr<BoolType> assertion) {
        checkNotNull(marker);
        checkNotNull(assertion);
        checkArgument(markers.toCollection().contains(marker), "Marker not found in solver");
        final Z3ItpMarker z3Marker = (Z3ItpMarker) marker;
        final BoolExpr term = (BoolExpr) transformationManager.toTerm(assertion);
        add(assertion, term);
        z3Marker.add(assertion);
    }

    @Override
    public Interpolant getInterpolant(ItpPattern pattern) {
        if (pattern instanceof Z3ItpPattern z3ItpPattern) {
            List<Z3ItpMarker> markers = z3ItpPattern.getSequence();
            List<AndExpr> terms =
                    markers.stream()
                            .map(z3ItpMarker -> z3ItpMarker.getTerms().stream().toList())
                            .map(AndExpr::create)
                            .toList();

            List<InterpolationMetadata> itpTasks =
                    IntStream.range(1, terms.size())
                            .mapToObj(
                                    i ->
                                            new InterpolationMetadata(
                                                    transformationManager,
                                                    terms.subList(0, i),
                                                    terms.subList(i, terms.size())))
                            .toList();

            List<BoolExpr> itps =
                    itpTasks.stream()
                            .map((InterpolationMetadata i) -> i.interpolate(z3Context))
                            .toList();

            Map<ItpMarker, Expr<BoolType>> itpMap = new LinkedHashMap<>();
            for (int i = 0; i < itps.size(); i++) {
                itpMap.put(markers.get(i), (Expr<BoolType>) termTransformer.toExpr(itps.get(i)));
            }
            itpMap.put(markers.get(markers.size() - 1), False());
            return new Z3Interpolant(itpMap);
        } else {
            throw new UnsupportedOperationException("Unsupported pattern: " + pattern);
        }
    }

    @Override
    public Collection<? extends ItpMarker> getMarkers() {
        return markers.toCollection();
    }

    ////

    private final class Z3Model extends Valuation {

        private final Model z3Model;
        private final Map<Decl<?>, LitExpr<?>> constToExpr;
        private volatile Collection<ConstDecl<?>> constDecls = null;

        public Z3Model(final Model z3Model) {
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

            @SuppressWarnings("unchecked")
            final LitExpr<DeclType> tVal = (LitExpr<DeclType>) val;
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
            final Expr<?> expr =
                    termTransformer.toFuncLitExpr(funcDecl, z3Model, new ArrayList<>());
            return (LitExpr<?>) expr;
        }

        private LitExpr<?> extractArrayLiteral(final FuncDecl funcDecl) {
            final Expr<?> expr =
                    termTransformer.toArrayLitExpr(funcDecl, z3Model, new ArrayList<>());
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

        private LitExpr<?> extractEnumLiteral(
                final ConstDecl<?> constDecl, final FuncDecl funcDecl) {
            final com.microsoft.z3.Expr term = z3Model.getConstInterp(funcDecl);
            if (term == null) {
                return null;
            } else {
                return EnumLitExpr.of((EnumType) constDecl.getType(), term.toString());
            }
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

        private Collection<ConstDecl<?>> constDeclsOf(final Model z3Model) {
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
