package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import org.junit.BeforeClass;
import org.junit.Test;

import java.nio.file.Path;

import static com.google.common.collect.ImmutableList.of;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public final class SmtLibSolverTest {
    private static SmtLibSolverFactory solverFactory;

    @BeforeClass
    public static void init() {
        solverFactory = SmtLibSolverFactory.create(
            Path.of("/home/vagrant/Vagrant/z3-4.8.8-x64-ubuntu-16.04/bin/z3"),
            new String[] { "-in", "-smt2" }
        );
    }

    @Test
    public void testSimple() {
        final Solver solver = solverFactory.createSolver();

        // Create two integer constants x and y
        final ConstDecl<IntType> cx = Const("x", Int());
        final ConstDecl<IntType> cy = Const("y", Int());

        // Add x == y + 1 to the solver
        solver.add(IntExprs.Eq(cx.getRef(), IntExprs.Add(cy.getRef(), Int(1))));

        // Check, the expression should be satisfiable
        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        // Add x < y to the solver
        solver.add(IntExprs.Lt(cx.getRef(), cy.getRef()));

        // Check, the expression should be unsatisfiable
        status = solver.check();
        assertTrue(status.isUnsat());
    }

    @Test
    public void testTrack() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BoolType> ca = Const("a", BoolExprs.Bool());
        final Expr<BoolType> expr = BoolExprs.And(ca.getRef(), True());

        solver.push();
        solver.track(expr);

        final SolverStatus status = solver.check();

        assertTrue(status.isSat());

        solver.pop();
    }

    @Test
    public void testUnsatCore() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<IntType> x = Const("x", IntExprs.Int());
        final ConstDecl<IntType> y = Const("y", IntExprs.Int());
        final Expr<BoolType> expr1 = IntExprs.Eq(x.getRef(), IntExprs.Int(0));
        final Expr<BoolType> expr2 = IntExprs.Eq(x.getRef(), IntExprs.Int(1));
        final Expr<BoolType> expr3 = IntExprs.Eq(y.getRef(), IntExprs.Int(1));

        solver.track(expr1);
        solver.track(expr2);
        solver.track(expr3);

        final SolverStatus status = solver.check();
        assertTrue(status.isUnsat());

        final var uc = solver.getUnsatCore();
        assertTrue(uc.contains(expr1));
        assertTrue(uc.contains(expr2));
        assertEquals(2, uc.size());
    }

    @Test
    public void testFunc() {
        // Arrange
        final Solver solver = solverFactory.createSolver();
        final ConstDecl<FuncType<IntType, IntType>> ca = Const("a", Func(Int(), Int()));
        final Expr<FuncType<IntType, IntType>> a = ca.getRef();
        final ParamDecl<IntType> px = Param("x", Int());
        final Expr<IntType> x = px.getRef();

        solver.add(BoolExprs.Forall(of(px), BoolExprs.Imply(IntExprs.Leq(x, Int(0)), IntExprs.Eq(App(a, x), Int(0)))));
        solver.add(BoolExprs.Forall(of(px), BoolExprs.Imply(IntExprs.Geq(x, Int(1)), IntExprs.Eq(App(a, x), Int(1)))));

        // Act
        final SolverStatus status = solver.check();
        assertTrue(status.isSat());
    }
}
