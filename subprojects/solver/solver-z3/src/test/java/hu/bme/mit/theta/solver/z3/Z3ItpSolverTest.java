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
package hu.bme.mit.theta.solver.z3;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;
import static hu.bme.mit.theta.solver.ItpMarkerTree.Leaf;
import static hu.bme.mit.theta.solver.ItpMarkerTree.Subtree;
import static hu.bme.mit.theta.solver.ItpMarkerTree.Tree;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpMarkerTree;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public final class Z3ItpSolverTest {

    ItpSolver solver;

    Expr<IntType> a;
    Expr<IntType> b;
    Expr<IntType> c;
    Expr<IntType> d;
    Expr<IntType> e;
    Expr<FuncType<IntType, IntType>> f;
    Expr<FuncType<IntType, IntType>> g;
    Expr<BvType> aBV;
    Expr<BvType> bBV;
    Expr<BvType> cBV;
    Expr<BvType> dBV;

    @BeforeEach
    public void initialize() {
        solver = Z3SolverFactory.getInstance().createItpSolver();

        final ConstDecl<IntType> ad = Const("a", Int());
        final ConstDecl<IntType> bd = Const("b", Int());
        final ConstDecl<IntType> cd = Const("c", Int());
        final ConstDecl<IntType> dd = Const("d", Int());
        final ConstDecl<IntType> ed = Const("e", Int());
        final ConstDecl<FuncType<IntType, IntType>> fd = Const("f", Func(Int(), Int()));
        final ConstDecl<FuncType<IntType, IntType>> gd = Const("g", Func(Int(), Int()));

        final ConstDecl<BvType> aBVd = Const("aBV", BvType.of(32));
        final ConstDecl<BvType> bBVd = Const("bBV", BvType.of(32));
        final ConstDecl<BvType> cBVd = Const("cBV", BvType.of(32));
        final ConstDecl<BvType> dBVd = Const("dBV", BvType.of(32));

        a = ad.getRef();
        b = bd.getRef();
        c = cd.getRef();
        d = dd.getRef();
        e = ed.getRef();
        f = fd.getRef();
        g = gd.getRef();

        aBV = aBVd.getRef();
        bBV = bBVd.getRef();
        cBV = cBVd.getRef();
        dBV = dBVd.getRef();
    }

    @Test
    public void testBinaryInterpolation() {
        final ItpMarker A = solver.createMarker();
        final ItpMarker B = solver.createMarker();
        final ItpPattern pattern = solver.createBinPattern(A, B);

        solver.add(A, Eq(a, b));
        solver.add(A, Eq(a, c));
        solver.add(B, Eq(b, d));
        solver.add(B, Neq(c, d));

        solver.check();
        Assertions.assertEquals(SolverStatus.UNSAT, solver.getStatus());
        final Interpolant itp = solver.getInterpolant(pattern);

        System.out.println(itp.eval(A));
        System.out.println("----------");
        Assertions.assertTrue(ExprUtils.getVars(itp.eval(A)).size() <= 3);
    }

    @Test
    public void testSequenceInterpolation() {
        final ItpMarker I1 = solver.createMarker();
        final ItpMarker I2 = solver.createMarker();
        final ItpMarker I3 = solver.createMarker();
        final ItpMarker I4 = solver.createMarker();
        final ItpMarker I5 = solver.createMarker();
        final List<ItpMarker> markers = ImmutableList.of(I1, I2, I3, I4, I5);
        final ItpPattern pattern = solver.createSeqPattern(markers);

        final Map<ItpMarker, List<Expr<BoolType>>> segments = new LinkedHashMap<>();
        segments.put(I1, List.of(Eq(a, Int(0))));
        segments.put(I2, List.of(Eq(a, b)));
        segments.put(I3, List.of(Eq(c, d)));
        segments.put(I4, List.of(Eq(d, Int(1))));
        segments.put(I5, List.of(Eq(b, c)));
        segments.forEach((m, es) -> es.forEach(e -> solver.add(m, e)));

        solver.check();
        Assertions.assertEquals(SolverStatus.UNSAT, solver.getStatus());

        assertInterpolantTree(solver.getInterpolant(pattern), chain(markers), segments);
    }

    @Test
    public void testTreeInterpolation() {
        final ItpMarker I1 = solver.createMarker();
        final ItpMarker I2 = solver.createMarker();
        final ItpMarker I3 = solver.createMarker();
        final ItpMarker I4 = solver.createMarker();
        final ItpMarker I5 = solver.createMarker();
        final ItpMarkerTree<ItpMarker> tree = Tree(I3, Subtree(I1, Leaf(I4), Leaf(I5)), Leaf(I2));
        final ItpPattern pattern = solver.createTreePattern(tree);

        final Map<ItpMarker, List<Expr<BoolType>>> segments = new LinkedHashMap<>();
        segments.put(I1, List.of(Eq(a, Int(0))));
        segments.put(I2, List.of(Eq(a, b)));
        segments.put(I3, List.of(Eq(c, d)));
        segments.put(I4, List.of(Eq(d, Int(1))));
        segments.put(I5, List.of(Eq(b, c)));
        segments.forEach((m, es) -> es.forEach(e -> solver.add(m, e)));

        solver.check();
        Assertions.assertEquals(SolverStatus.UNSAT, solver.getStatus());

        assertInterpolantTree(solver.getInterpolant(pattern), tree, segments);
    }

    //    @Test
    public void testEUF() {
        final ItpMarker A = solver.createMarker();
        final ItpMarker B = solver.createMarker();
        final ItpPattern pattern = solver.createBinPattern(A, B);

        solver.add(A, Eq(App(f, a), c));
        solver.add(A, Eq(App(f, b), d));
        solver.add(B, Eq(a, b));
        solver.add(B, Neq(App(g, c), App(g, d)));

        solver.check();
        Assertions.assertEquals(SolverStatus.UNSAT, solver.getStatus());
        final Interpolant itp = solver.getInterpolant(pattern);

        System.out.println(itp.eval(A));
        System.out.println("----------");
    }

    @Test
    public void testLIA() {
        final ItpMarker A = solver.createMarker();
        final ItpMarker B = solver.createMarker();
        final ItpPattern pattern = solver.createBinPattern(A, B);

        solver.add(A, Eq(b, Mul(ImmutableList.of(Int(2), a))));
        solver.add(B, Eq(b, Add(ImmutableList.of(Mul(ImmutableList.of(Int(2), c)), Int(1)))));

        solver.check();
        Assertions.assertEquals(SolverStatus.UNSAT, solver.getStatus());
        final Interpolant itp = solver.getInterpolant(pattern);

        System.out.println(itp.eval(A));
        System.out.println("----------");
    }

    @Test
    public void testBV() {
        final ItpMarker I1 = solver.createMarker();
        final ItpMarker I2 = solver.createMarker();
        final ItpMarker I3 = solver.createMarker();
        final ItpMarker I4 = solver.createMarker();
        final ItpMarker I5 = solver.createMarker();
        final ItpPattern pattern = solver.createSeqPattern(ImmutableList.of(I1, I2, I3, I4, I5));

        final var one =
                BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ONE, aBV.getType().getSize());
        final var zero =
                BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, aBV.getType().getSize());

        solver.add(I1, BvExprs.Eq(aBV, zero));
        solver.add(I2, BvExprs.Eq(aBV, bBV));
        solver.add(I3, BvExprs.Eq(cBV, dBV));
        solver.add(I4, BvExprs.Eq(dBV, one));
        solver.add(I5, BvExprs.Eq(bBV, cBV));

        solver.check();
        Assertions.assertEquals(SolverStatus.UNSAT, solver.getStatus());
        final Interpolant itp = solver.getInterpolant(pattern);

        System.out.println(itp.eval(I1));
        System.out.println(itp.eval(I2));
        System.out.println(itp.eval(I3));
        System.out.println(itp.eval(I4));
        System.out.println(itp.eval(I5));
        System.out.println("----------");
    }

    //     @Test
    public void testQuantifiers() {
        final ItpMarker A = solver.createMarker();
        final ItpMarker B = solver.createMarker();
        final ItpPattern pattern = solver.createBinPattern(A, B);

        final ConstDecl<IntType> id = Const("i", Int());
        final ConstDecl<FuncType<IntType, BoolType>> pd = Const("p", Func(Int(), Bool()));
        final ConstDecl<FuncType<IntType, BoolType>> qd = Const("q", Func(Int(), Bool()));
        final ParamDecl<IntType> x1d = Param("x", Int());
        final ParamDecl<IntType> x2d = Param("x", Int());

        final Expr<IntType> i = id.getRef();
        final Expr<FuncType<IntType, BoolType>> p = pd.getRef();
        final Expr<FuncType<IntType, BoolType>> q = qd.getRef();
        final Expr<IntType> x1 = x1d.getRef();
        final Expr<IntType> x2 = x2d.getRef();

        solver.add(A, Forall(ImmutableList.of(x1d), Imply(App(q, x1), App(p, x1))));
        solver.add(A, Forall(ImmutableList.of(x2d), Not(App(p, x2))));
        solver.add(B, App(q, i));

        solver.check();
        Assertions.assertEquals(SolverStatus.UNSAT, solver.getStatus());
        final Interpolant itp = solver.getInterpolant(pattern);

        System.out.println(itp.eval(A));
        System.out.println("----------");
    }

    @Test
    public void testPushPop() {
        final ItpMarker A = solver.createMarker();
        final ItpMarker B = solver.createMarker();
        final ItpPattern pattern = solver.createBinPattern(A, B);

        solver.add(A, Eq(a, b));
        solver.add(B, Eq(b, c));

        solver.push();

        solver.add(A, Neq(a, c));
        solver.check();
        Assertions.assertEquals(SolverStatus.UNSAT, solver.getStatus());

        solver.pop();

        solver.add(B, Neq(a, c));
        solver.check();
        Assertions.assertEquals(SolverStatus.UNSAT, solver.getStatus());
        final Interpolant itp = solver.getInterpolant(pattern);

        // The pop took `a != c` off A; an interpolant computed over the popped assertion as well
        // is not an interpolant of what is left.
        assertInterpolant(itp.eval(A), List.of(Eq(a, b)), List.of(Eq(b, c), Neq(a, c)));
    }

    @Test
    public void testInterpolationWithoutCommonConstants() {
        final ItpMarker A = solver.createMarker();
        final ItpMarker B = solver.createMarker();
        final ItpPattern pattern = solver.createBinPattern(A, B);

        // The two sides share no constant, so the interpolant ranges over none either.
        solver.add(A, Lt(a, Int(0)));
        solver.add(A, Gt(a, Int(0)));
        solver.add(B, Eq(b, Int(1)));

        solver.check();
        Assertions.assertEquals(SolverStatus.UNSAT, solver.getStatus());
        final Interpolant itp = solver.getInterpolant(pattern);

        assertInterpolant(
                itp.eval(A), List.of(Lt(a, Int(0)), Gt(a, Int(0))), List.of(Eq(b, Int(1))));
    }

    /** Checks the defining property of an interpolant: A entails it, and it contradicts B. */
    private static void assertInterpolant(
            final Expr<BoolType> itp,
            final Collection<Expr<BoolType>> aExprs,
            final Collection<Expr<BoolType>> bExprs) {
        Assertions.assertNotNull(itp);

        final Solver aCheck = Z3SolverFactory.getInstance().createSolver();
        aExprs.forEach(aCheck::add);
        aCheck.add(Not(itp));
        Assertions.assertEquals(
                SolverStatus.UNSAT, aCheck.check(), "A does not entail the interpolant: " + itp);

        final Solver bCheck = Z3SolverFactory.getInstance().createSolver();
        bExprs.forEach(bCheck::add);
        bCheck.add(itp);
        Assertions.assertEquals(
                SolverStatus.UNSAT, bCheck.check(), "The interpolant is consistent with B: " + itp);
    }

    /**
     * The chain {@link ItpSolver#createSeqPattern} builds: the first marker is the deepest leaf.
     */
    private static ItpMarkerTree<ItpMarker> chain(final List<ItpMarker> markers) {
        ItpMarkerTree<ItpMarker> current = Leaf(markers.get(0));
        for (int i = 1; i < markers.size(); i++) {
            current = Tree(markers.get(i), current);
        }
        return current;
    }

    /**
     * Checks the tree-interpolant contract at every node: the node's own subtree entails it, it
     * contradicts the rest of the pattern, it follows from its children plus the node's own
     * assertions, and it only mentions constants the two sides share. A sequence pattern is the
     * chain case of this, and a binary pattern the two-node chain.
     */
    private static void assertInterpolantTree(
            final Interpolant itp,
            final ItpMarkerTree<ItpMarker> root,
            final Map<ItpMarker, List<Expr<BoolType>>> segments) {
        checkNode(itp, root, root, segments);
    }

    private static void checkNode(
            final Interpolant itp,
            final ItpMarkerTree<ItpMarker> node,
            final ItpMarkerTree<ItpMarker> root,
            final Map<ItpMarker, List<Expr<BoolType>>> segments) {
        for (final ItpMarkerTree<ItpMarker> child : node.getChildren()) {
            checkNode(itp, child, root, segments);
        }

        final Set<ItpMarker> subtree = new LinkedHashSet<>();
        collectMarkers(node, subtree);
        final List<Expr<BoolType>> sub = assertionsOf(subtree, segments);
        final Set<ItpMarker> others = new LinkedHashSet<>(segments.keySet());
        others.removeAll(subtree);
        final List<Expr<BoolType>> rest = assertionsOf(others, segments);

        final Expr<BoolType> current = itp.eval(node.getMarker());
        Assertions.assertNotNull(current, "No interpolant for a marker of the pattern");

        assertUnsat(
                concat(sub, List.of(Not(current))),
                "The subtree does not entail its interpolant: " + current);
        assertUnsat(
                concat(rest, List.of(current)),
                "The interpolant is consistent with the rest of the pattern: " + current);

        final List<Expr<BoolType>> inductive = new ArrayList<>();
        for (final ItpMarkerTree<ItpMarker> child : node.getChildren()) {
            inductive.add(itp.eval(child.getMarker()));
        }
        inductive.addAll(segments.get(node.getMarker()));
        inductive.add(Not(current));
        assertUnsat(inductive, "The interpolant does not follow from its children: " + current);

        final Set<ConstDecl<?>> scope = new LinkedHashSet<>(ExprUtils.getConstants(And(sub)));
        scope.retainAll(ExprUtils.getConstants(And(rest)));
        Assertions.assertTrue(
                scope.containsAll(ExprUtils.getConstants(current)),
                "The interpolant is out of scope: " + current + " not within " + scope);
    }

    private static void collectMarkers(
            final ItpMarkerTree<ItpMarker> node, final Set<ItpMarker> into) {
        into.add(node.getMarker());
        node.getChildren().forEach(child -> collectMarkers(child, into));
    }

    private static List<Expr<BoolType>> assertionsOf(
            final Set<ItpMarker> markers, final Map<ItpMarker, List<Expr<BoolType>>> segments) {
        final List<Expr<BoolType>> result = new ArrayList<>();
        segments.forEach(
                (marker, exprs) -> {
                    if (markers.contains(marker)) {
                        result.addAll(exprs);
                    }
                });
        return result;
    }

    private static List<Expr<BoolType>> concat(
            final List<Expr<BoolType>> a, final List<Expr<BoolType>> b) {
        final List<Expr<BoolType>> result = new ArrayList<>(a);
        result.addAll(b);
        return result;
    }

    private static void assertUnsat(final List<Expr<BoolType>> exprs, final String message) {
        final Solver checker = Z3SolverFactory.getInstance().createSolver();
        exprs.forEach(checker::add);
        Assertions.assertEquals(SolverStatus.UNSAT, checker.check(), message);
    }
}
