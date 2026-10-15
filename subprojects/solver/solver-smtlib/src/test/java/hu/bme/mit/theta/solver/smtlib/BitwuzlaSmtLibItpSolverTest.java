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
package hu.bme.mit.theta.solver.smtlib;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.UGt;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.ULt;
import static hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToNeutralBvLitExpr;
import static hu.bme.mit.theta.solver.ItpMarkerTree.Leaf;
import static hu.bme.mit.theta.solver.ItpMarkerTree.Tree;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.smtlib.testing.SolverInstallations;
import java.math.BigInteger;
import java.util.List;
import java.util.Set;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Bitwuzla is bit-vector oriented and has no integer arithmetic, so these tests are phrased over
 * {@link BvType}.
 */
public final class BitwuzlaSmtLibItpSolverTest {

    private static final String SOLVER = "bitwuzla";
    private static final String VERSION = "0.9.1";
    private static final int SIZE = 8;

    private static SolverFactory solverFactory;

    private ItpSolver solver;

    private ConstDecl<BvType> xd;
    private ConstDecl<BvType> yd;
    private Expr<BvType> x;
    private Expr<BvType> y;

    @BeforeAll
    public static void init() {
        solverFactory = SolverInstallations.installOrSkip(SOLVER, VERSION);
    }

    @BeforeEach
    public void initialize() {
        Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX));

        solver = solverFactory.createItpSolver();

        xd = Const("x", BvType(SIZE));
        yd = Const("y", BvType(SIZE));
        x = xd.getRef();
        y = yd.getRef();
    }

    @AfterEach
    public void tearDown() throws Exception {
        if (solver != null) {
            solver.close();
        }
    }

    /** A and B share only y, so the interpolant has to be a statement about y alone. */
    @Test
    public void testBinaryInterpolation() throws Exception {
        final ItpMarker markerA = solver.createMarker();
        final ItpMarker markerB = solver.createMarker();
        final ItpPattern pattern = solver.createBinPattern(markerA, markerB);

        final Expr<BoolType> a1 = ULt(x, bv(5));
        final Expr<BoolType> a2 = ULt(y, x);
        final Expr<BoolType> b1 = UGt(y, bv(10));

        solver.add(markerA, a1);
        solver.add(markerA, a2);
        solver.add(markerB, b1);

        assertEquals(SolverStatus.UNSAT, solver.check());
        final Interpolant itp = solver.getInterpolant(pattern);
        final Expr<BoolType> interpolant = itp.eval(markerA);
        System.out.println("interpolant: " + interpolant);

        assertTrue(
                Set.of(yd).containsAll(ExprUtils.getConstants(interpolant)),
                "The interpolant may only mention the shared constant y: " + interpolant);
        assertImplied(ImmutableList.of(a1, a2), interpolant);
        assertUnsat(ImmutableList.of(interpolant, b1));
    }

    /** With everything on the A side the only interpolant is false. */
    @Test
    public void testInterpolantOfAnUnsatASide() throws Exception {
        final ItpMarker markerA = solver.createMarker();
        final ItpMarker markerB = solver.createMarker();
        final ItpPattern pattern = solver.createBinPattern(markerA, markerB);

        final Expr<BoolType> a1 = ULt(y, bv(5));
        final Expr<BoolType> a2 = UGt(y, bv(10));

        solver.add(markerA, a1);
        solver.add(markerA, a2);

        assertEquals(SolverStatus.UNSAT, solver.check());
        final Expr<BoolType> interpolant = solver.getInterpolant(pattern).eval(markerA);
        System.out.println("interpolant: " + interpolant);

        assertUnsat(ImmutableList.of(interpolant));
    }

    @Test
    public void testPushPop() throws Exception {
        final ItpMarker markerA = solver.createMarker();
        final ItpMarker markerB = solver.createMarker();
        final ItpPattern pattern = solver.createBinPattern(markerA, markerB);

        solver.add(markerA, ULt(x, bv(5)));

        solver.push();
        solver.add(markerA, UGt(x, bv(10)));
        assertEquals(SolverStatus.UNSAT, solver.check());
        solver.pop();

        final Expr<BoolType> b1 = UGt(y, bv(10));
        solver.add(markerA, ULt(y, x));
        solver.add(markerB, b1);

        assertEquals(SolverStatus.UNSAT, solver.check());
        final Expr<BoolType> interpolant = solver.getInterpolant(pattern).eval(markerA);
        System.out.println("interpolant: " + interpolant);

        assertTrue(
                Set.of(yd).containsAll(ExprUtils.getConstants(interpolant)),
                "The interpolant may only mention the shared constant y: " + interpolant);
        assertUnsat(ImmutableList.of(interpolant, b1));
    }

    @Test
    public void testSequenceInterpolation() throws Exception {
        final List<ItpMarker> sequence =
                ImmutableList.of(
                        solver.createMarker(), solver.createMarker(), solver.createMarker());
        final ItpPattern pattern = solver.createSeqPattern(sequence);
        final List<Expr<BoolType>> formulas =
                ImmutableList.of(ULt(x, bv(5)), ULt(y, x), UGt(y, bv(10)));

        for (var i = 0; i < sequence.size(); i++) {
            solver.add(sequence.get(i), formulas.get(i));
        }

        assertEquals(SolverStatus.UNSAT, solver.check());
        final Interpolant itp = solver.getInterpolant(pattern);

        // Every cut is a binary interpolant of the prefix against the suffix; the sequence is not
        // claimed to be inductive.
        for (var i = 0; i < sequence.size(); i++) {
            final Expr<BoolType> interpolant = itp.eval(sequence.get(i));
            System.out.println("sequence interpolant " + i + ": " + interpolant);

            assertImplied(formulas.subList(0, i + 1), interpolant);
            assertUnsat(
                    ImmutableList.<Expr<BoolType>>builder()
                            .add(interpolant)
                            .addAll(formulas.subList(i + 1, formulas.size()))
                            .build());
        }
        assertEquals(False(), itp.eval(sequence.get(sequence.size() - 1)));
    }

    @Test
    public void testBranchingTreePatternIsRejected() {
        final ItpMarker i1 = solver.createMarker();
        final ItpMarker i2 = solver.createMarker();
        final ItpMarker i3 = solver.createMarker();
        final ItpPattern pattern = solver.createTreePattern(Tree(i3, Leaf(i1), Leaf(i2)));

        solver.add(i1, ULt(x, bv(5)));
        solver.add(i2, ULt(y, x));
        solver.add(i3, UGt(y, bv(10)));

        assertEquals(SolverStatus.UNSAT, solver.check());
        final var exception =
                assertThrows(
                        UnsupportedOperationException.class, () -> solver.getInterpolant(pattern));
        assertTrue(exception.getMessage().contains("branches"), exception.getMessage());
    }

    /**
     * An assertion outside the pattern would silently join the B side, which is not interpolation.
     */
    @Test
    public void testMarkerOutsideThePatternIsRejected() {
        final ItpMarker markerA = solver.createMarker();
        final ItpMarker markerB = solver.createMarker();
        final ItpMarker outside = solver.createMarker();
        final ItpPattern pattern = solver.createBinPattern(markerA, markerB);

        solver.add(markerA, ULt(x, bv(5)));
        solver.add(markerB, UGt(y, bv(10)));
        solver.add(outside, ULt(y, x));

        assertEquals(SolverStatus.UNSAT, solver.check());
        assertThrows(UnsupportedOperationException.class, () -> solver.getInterpolant(pattern));
    }

    private Expr<BvType> bv(final int value) {
        return bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(value), SIZE);
    }

    /**
     * Checks {@code premises => consequence} the only way a solver can: by refuting the negation.
     */
    private void assertImplied(
            final Iterable<? extends Expr<BoolType>> premises, final Expr<BoolType> consequence)
            throws Exception {
        try (final Solver checker = solverFactory.createSolver()) {
            checker.add(premises);
            checker.add(Not(consequence));
            assertEquals(SolverStatus.UNSAT, checker.check());
        }
    }

    private void assertUnsat(final Iterable<? extends Expr<BoolType>> exprs) throws Exception {
        try (final Solver checker = solverFactory.createSolver()) {
            checker.add(exprs);
            assertEquals(SolverStatus.UNSAT, checker.check());
        }
    }
}
