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
package hu.bme.mit.theta.solver;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import com.google.common.collect.Sets;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.Relation;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.impl.StackImpl;
import java.util.*;

public class HornItpSolver implements ItpSolver {

    private final Solver solver;
    private final HornSolver hornSolver;
    private final Stack<HornItpMarker> markers;

    public HornItpSolver(Solver solver, HornSolver hornSolver) {
        this.solver = solver;
        this.hornSolver = hornSolver;
        markers = new StackImpl<>();
    }

    @Override
    public ItpPattern createTreePattern(final ItpMarkerTree<? extends ItpMarker> root) {
        if (root.getMarker() instanceof HornItpMarker) {
            return new HornItpPattern((ItpMarkerTree<HornItpMarker>) root);
        } else {
            throw new UnsupportedOperationException(
                    "Cannot create tree pattern due to marker type: "
                            + root.getMarker().getClass().getName());
        }
    }

    @Override
    public ItpMarker createMarker() {
        return new HornItpMarker();
    }

    @Override
    public void add(final ItpMarker marker, final Expr<BoolType> assertion) {
        if (marker instanceof HornItpMarker hornItpMarker) {
            hornItpMarker.add(assertion);
            solver.add(assertion);
        } else {
            throw new UnsupportedOperationException(
                    "Cannot add assertion to marker due to type: " + marker.getClass().getName());
        }
    }

    @Override
    public Interpolant getInterpolant(final ItpPattern pattern) {
        if (pattern instanceof HornItpPattern hornPattern) {
            final var root = hornPattern.getRoot();
            if (root.getChildrenNumber() == 1
                    && root.getChildren().get(0).getChildrenNumber() == 0) {
                final var B = root.getMarker(); // root always false (?)
                final var A = root.getChildren().get(0).getMarker();

                final var symbolsA = ExprUtils.getConstants(A.getTerms());
                final var symbolsB = ExprUtils.getConstants(B.getTerms());

                final var commonSymbols =
                        Sets.intersection(symbolsA, symbolsB).toArray(ConstDecl[]::new);

                final var itp =
                        new Relation(
                                "__itp__rel__",
                                Arrays.stream(commonSymbols)
                                        .map(ConstDecl::getType)
                                        .toArray(Type[]::new));

                final var a = A.getRelation();
                final var b = B.getRelation();

                final var paramsA =
                        Arrays.stream(commonSymbols)
                                .map(
                                        constDecl ->
                                                Arrays.stream(a.get2())
                                                        .filter(
                                                                it ->
                                                                        it.getName()
                                                                                        .equals(
                                                                                                constDecl
                                                                                                        .getName())
                                                                                && it.getType()
                                                                                        .equals(
                                                                                                constDecl
                                                                                                        .getType()))
                                                        .findFirst()
                                                        .get()
                                                        .getRef())
                                .toArray(RefExpr[]::new);

                final var paramsB =
                        Arrays.stream(commonSymbols)
                                .map(
                                        constDecl ->
                                                Arrays.stream(b.get2())
                                                        .filter(
                                                                it ->
                                                                        it.getName()
                                                                                        .equals(
                                                                                                constDecl
                                                                                                        .getName())
                                                                                && it.getType()
                                                                                        .equals(
                                                                                                constDecl
                                                                                                        .getType()))
                                                        .findFirst()
                                                        .get()
                                                        .getRef())
                                .toArray(RefExpr[]::new);

                itp.invoke(paramsA)
                        .plusAssign(
                                a.get1()
                                        .invoke(
                                                Arrays.stream(a.get2())
                                                        .map(ParamDecl::getRef)
                                                        .toArray(RefExpr[]::new))
                                        .getExpr());
                (itp.invoke(paramsB)
                                .with(
                                        b.get1()
                                                .invoke(
                                                        Arrays.stream(b.get2())
                                                                .map(ParamDecl::getRef)
                                                                .toArray(RefExpr[]::new))
                                                .getExpr()))
                        .not();

                hornSolver.push();
                hornSolver.add(a.get1());
                hornSolver.add(b.get1());
                hornSolver.add(itp);
                final var status = hornSolver.check();
                checkState(status.isSat(), "ITP task should be SAT");
                Expr<?> itpSolution = hornSolver.getModel().toMap().get(itp.getConstDecl());
                final var params = new ArrayList<ParamDecl<?>>();
                while (itpSolution instanceof FuncLitExpr<?, ?> funcLitExpr) {
                    params.add(funcLitExpr.getParam());
                    itpSolution = funcLitExpr.getResult();
                }
                final var declMap = new LinkedHashMap<Decl<?>, Decl<?>>();
                for (int i = 0; i < params.size(); i++) {
                    declMap.put(params.get(i), commonSymbols[i]);
                }
                itpSolution = ExprUtils.changeDecls(itpSolution, declMap);
                hornSolver.pop();
                return new HornInterpolant(Map.of(A, (Expr<BoolType>) itpSolution, B, False()));
            }

            throw new UnsupportedOperationException(
                    "Can only handle binary interpolation right now.");
        } else {
            throw new UnsupportedOperationException(
                    "Cannot get interpolant due to pattern type: " + pattern.getClass().getName());
        }
    }

    @Override
    public Collection<? extends ItpMarker> getMarkers() {
        return markers.toCollection();
    }

    @Override
    public SolverStatus check() {
        return solver.check();
    }

    @Override
    public void push() {
        solver.push();
        hornSolver.push();
        markers.toCollection().forEach(HornItpMarker::push);
        markers.push();
    }

    @Override
    public void pop(int n) {
        solver.pop(n);
        hornSolver.pop(n);
        markers.toCollection().forEach(it -> it.pop(n));
        markers.pop(n);
    }

    @Override
    public void reset() {
        solver.reset();
        hornSolver.reset();
        markers.clear();
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
    public void close() throws Exception {
        solver.close();
        hornSolver.close();
    }

    static final class HornItpMarker implements ItpMarker {
        private static int COUNTER = 0;
        private final String prefix = "ItpMarker" + COUNTER++ + "_";

        private final Stack<Expr<BoolType>> terms;

        public HornItpMarker() {
            terms = new StackImpl<>();
        }

        public void add(final Expr<BoolType> term) {
            terms.add(checkNotNull(term));
        }

        public void push() {
            terms.push();
        }

        public void pop(final int n) {
            terms.pop(n);
        }

        public Collection<Expr<BoolType>> getTerms() {
            return terms.toCollection();
        }

        public Tuple2<Relation, ParamDecl[]> getRelation() {
            final var currentTerms = terms.toCollection();
            final var symbols = ExprUtils.getConstants(currentTerms).stream().toList();
            final var types = symbols.stream().map(Decl::getType).toArray(Type[]::new);
            final var params =
                    symbols.stream()
                            .map(constDecl -> Param(constDecl.getName(), constDecl.getType()))
                            .toArray(ParamDecl[]::new);
            final Map<Decl<?>, Decl<?>> declMap = new LinkedHashMap<>();
            for (int i = 0; i < symbols.size(); i++) {
                declMap.put(symbols.get(i), params[i]);
            }
            Relation rel = new Relation(prefix, types);
            currentTerms.forEach(
                    it ->
                            rel.invoke(
                                            Arrays.stream(params)
                                                    .map(Decl::getRef)
                                                    .toArray(RefExpr[]::new))
                                    .plusAssign(ExprUtils.changeDecls(it, declMap)));

            return Tuple2.of(rel, params);
        }
    }

    static final class HornItpPattern implements ItpPattern.Tree<HornItpMarker> {
        final ItpMarkerTree<HornItpMarker> markerTree;

        public HornItpPattern(final ItpMarkerTree<HornItpMarker> markerTree) {
            this.markerTree = markerTree;
        }

        @Override
        public ItpMarkerTree<HornItpMarker> getRoot() {
            return markerTree;
        }
    }

    static final class HornInterpolant implements Interpolant {

        private final Map<ItpMarker, Expr<BoolType>> itpMap;

        HornInterpolant(final Map<ItpMarker, Expr<BoolType>> itpMap) {
            this.itpMap = itpMap;
        }

        @Override
        public Expr<BoolType> eval(final ItpMarker marker) {
            checkNotNull(marker);
            final Expr<BoolType> itpExpr = itpMap.get(marker);
            checkNotNull(itpExpr);
            return itpExpr;
        }
    }
}
