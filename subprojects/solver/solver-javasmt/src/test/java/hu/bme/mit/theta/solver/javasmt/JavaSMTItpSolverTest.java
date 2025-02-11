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
package hu.bme.mit.theta.solver.javasmt;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;
import static hu.bme.mit.theta.solver.ItpMarkerTree.Leaf;
import static hu.bme.mit.theta.solver.ItpMarkerTree.Subtree;
import static hu.bme.mit.theta.solver.ItpMarkerTree.Tree;
import static org.junit.Assume.assumeFalse;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.OsHelper.OperatingSystem;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverStatus;
import java.util.Collection;
import java.util.List;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

@RunWith(Parameterized.class)
public final class JavaSMTItpSolverTest {
    @Parameter(0)
    public Solvers solver;

    @Parameter(1)
    public ItpSolver itpSolver;

    Expr<IntType> a;
    Expr<IntType> b;
    Expr<IntType> c;
    Expr<IntType> d;
    Expr<IntType> e;
    Expr<FuncType<IntType, IntType>> f;
    Expr<FuncType<IntType, IntType>> g;

    @Parameters(name = "solver: {0}")
    public static Collection<?> operations() {
        if (OsHelper.getOs().equals(OperatingSystem.LINUX)) {
            return List.of(
                    new Object[] {
                        Solvers.SMTINTERPOL,
                        JavaSMTSolverFactory.create(Solvers.SMTINTERPOL, new String[] {})
                                .createItpSolver()
                    },
                    new Object[] {
                        Solvers.PRINCESS,
                        JavaSMTSolverFactory.create(Solvers.PRINCESS, new String[] {})
                                .createItpSolver()
                    },
                    new Object[] {
                        Solvers.CVC5,
                        JavaSMTSolverFactory.create(Solvers.CVC5, new String[] {}).createItpSolver()
                    });
        } else {
            return List.of(
                    new Object[] {
                        Solvers.SMTINTERPOL,
                        JavaSMTSolverFactory.create(Solvers.SMTINTERPOL, new String[] {})
                                .createItpSolver()
                    },
                    new Object[] {
                        Solvers.PRINCESS,
                        JavaSMTSolverFactory.create(Solvers.PRINCESS, new String[] {})
                                .createItpSolver()
                    });
        }
    }

    @Before
    public void initialize() {
        final ConstDecl<IntType> ad = Const("a", Int());
        final ConstDecl<IntType> bd = Const("b", Int());
        final ConstDecl<IntType> cd = Const("c", Int());
        final ConstDecl<IntType> dd = Const("d", Int());
        final ConstDecl<IntType> ed = Const("e", Int());
        final ConstDecl<FuncType<IntType, IntType>> fd = Const("f", Func(Int(), Int()));
        final ConstDecl<FuncType<IntType, IntType>> gd = Const("g", Func(Int(), Int()));

        a = ad.getRef();
        b = bd.getRef();
        c = cd.getRef();
        d = dd.getRef();
        e = ed.getRef();
        f = fd.getRef();
        g = gd.getRef();
    }

    @Test
    public void testBinaryInterpolation() {
        final ItpMarker A = itpSolver.createMarker();
        final ItpMarker B = itpSolver.createMarker();
        final ItpPattern pattern = itpSolver.createBinPattern(A, B);

        itpSolver.add(A, Eq(a, b));
        itpSolver.add(A, Eq(a, c));
        itpSolver.add(B, Eq(b, d));
        itpSolver.add(B, Neq(c, d));

        itpSolver.check();
        Assert.assertEquals(SolverStatus.UNSAT, itpSolver.getStatus());
        final Interpolant itp = itpSolver.getInterpolant(pattern);

        System.out.println(itp.eval(A));
        System.out.println("----------");
        Assert.assertTrue(ExprUtils.getVars(itp.eval(A)).size() <= 3);
    }

    @Test
    public void testSequenceInterpolation() {
        final ItpMarker I1 = itpSolver.createMarker();
        final ItpMarker I2 = itpSolver.createMarker();
        final ItpMarker I3 = itpSolver.createMarker();
        final ItpMarker I4 = itpSolver.createMarker();
        final ItpMarker I5 = itpSolver.createMarker();
        final ItpPattern pattern = itpSolver.createSeqPattern(ImmutableList.of(I1, I2, I3, I4, I5));

        itpSolver.add(I1, Eq(a, Int(0)));
        itpSolver.add(I2, Eq(a, b));
        itpSolver.add(I3, Eq(c, d));
        itpSolver.add(I4, Eq(d, Int(1)));
        itpSolver.add(I5, Eq(b, c));

        itpSolver.check();
        Assert.assertEquals(SolverStatus.UNSAT, itpSolver.getStatus());
        final Interpolant itp = itpSolver.getInterpolant(pattern);

        System.out.println(itp.eval(I1));
        System.out.println(itp.eval(I2));
        System.out.println(itp.eval(I3));
        System.out.println(itp.eval(I4));
        System.out.println(itp.eval(I5));
        System.out.println("----------");
    }

    @Test
    public void testTreeInterpolation() {
        assumeFalse(solver == Solvers.CVC5);

        final ItpMarker I1 = itpSolver.createMarker();
        final ItpMarker I2 = itpSolver.createMarker();
        final ItpMarker I3 = itpSolver.createMarker();
        final ItpMarker I4 = itpSolver.createMarker();
        final ItpMarker I5 = itpSolver.createMarker();
        final ItpPattern pattern =
                itpSolver.createTreePattern(Tree(I3, Subtree(I1, Leaf(I4), Leaf(I5)), Leaf(I2)));

        itpSolver.add(I1, Eq(a, Int(0)));
        itpSolver.add(I2, Eq(a, b));
        itpSolver.add(I3, Eq(c, d));
        itpSolver.add(I4, Eq(d, Int(1)));
        itpSolver.add(I5, Eq(b, c));

        itpSolver.check();
        Assert.assertEquals(SolverStatus.UNSAT, itpSolver.getStatus());
        final Interpolant itp = itpSolver.getInterpolant(pattern);

        System.out.println(itp.eval(I1));
        System.out.println(itp.eval(I2));
        System.out.println(itp.eval(I3));
        System.out.println(itp.eval(I4));
        System.out.println(itp.eval(I5));
        System.out.println("----------");
    }

    @Test
    public void testLIA() {
        assumeFalse(solver == Solvers.CVC5);

        final ItpMarker A = itpSolver.createMarker();
        final ItpMarker B = itpSolver.createMarker();
        final ItpPattern pattern = itpSolver.createBinPattern(A, B);

        itpSolver.add(A, Eq(b, Mul(ImmutableList.of(Int(2), a))));
        itpSolver.add(B, Eq(b, Add(ImmutableList.of(Mul(ImmutableList.of(Int(2), c)), Int(1)))));

        itpSolver.check();
        Assert.assertEquals(SolverStatus.UNSAT, itpSolver.getStatus());
        final Interpolant itp = itpSolver.getInterpolant(pattern);

        System.out.println(itp.eval(A));
        System.out.println("----------");
    }

    @Test
    public void testQuantifiers() {
        assumeFalse(solver == Solvers.SMTINTERPOL);
        assumeFalse(solver == Solvers.CVC5);

        final ItpMarker A = itpSolver.createMarker();
        final ItpMarker B = itpSolver.createMarker();
        final ItpPattern pattern = itpSolver.createBinPattern(A, B);

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

        itpSolver.add(A, Forall(ImmutableList.of(x1d), Imply(App(q, x1), App(p, x1))));
        itpSolver.add(A, Forall(ImmutableList.of(x2d), Not(App(p, x2))));
        itpSolver.add(B, App(q, i));

        itpSolver.check();
        Assert.assertEquals(SolverStatus.UNSAT, itpSolver.getStatus());
        final Interpolant itp = itpSolver.getInterpolant(pattern);

        System.out.println(itp.eval(A));
        System.out.println("----------");
    }

    @Test
    public void testPushPop() {
        final ItpMarker A = itpSolver.createMarker();
        final ItpMarker B = itpSolver.createMarker();
        final ItpPattern pattern = itpSolver.createBinPattern(A, B);

        itpSolver.add(A, Eq(a, b));
        itpSolver.add(B, Eq(b, c));

        itpSolver.push();

        itpSolver.add(A, Neq(a, c));
        itpSolver.check();
        Assert.assertEquals(SolverStatus.UNSAT, itpSolver.getStatus());

        itpSolver.pop();

        itpSolver.add(B, Neq(a, c));
        itpSolver.check();
        Assert.assertEquals(SolverStatus.UNSAT, itpSolver.getStatus());
        final Interpolant itp = itpSolver.getInterpolant(pattern);

        System.out.println(itp.eval(A));
        System.out.println("----------");
    }
}
