package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import org.junit.AfterClass;
import org.junit.Assume;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static com.google.common.collect.ImmutableList.of;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public final class SmtLibSolverTest {
    private static boolean solverInstalled = false;
    private static SmtLibSolverManager solverManager;
    private static SolverFactory solverFactory;

    @BeforeClass
    public static void init() throws SmtLibSolverInstallerException, IOException {
        if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
            Path home = SmtLibSolverManager.HOME;

            solverManager = SmtLibSolverManager.create(home, NullLogger.getInstance());
            try {
                solverManager.install("z3", "4.5.0", "4.5.0", null, false);
                solverInstalled = true;
            } catch (SmtLibSolverInstallerException e) {
            }

            solverFactory = solverManager.getSolverFactory("z3", "4.5.0");
        }
    }

    @AfterClass
    public static void destroy() throws SmtLibSolverInstallerException {
        if(solverInstalled) solverManager.uninstall("z3", "4.5.0");
    }

    @Before
    public void before() {
        Assume.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX));
    }

    @Test
    public void test() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);

        final var x = Const("x", BvExprs.BvType(4));
        symbolTable.put(x, "x", "(declare-fun x () (_ BitVec 4))");

        final var expr = termTransformer.toExpr(
                "(forall ((y (Array (_ BitVec 4) Int))) (= (select y x) 0))",
                BoolExprs.Bool(), new SmtLibModel(Map.of())
        );
        assertNotNull(expr);
        assertTrue(expr instanceof ForallExpr);
        assertEquals(Array(x.getType(), IntExprs.Int()), ((ForallExpr) expr).getParamDecls().get(0).getType());
    }

    @Test
    public void testSimple() {
        final Solver solver = solverFactory.createSolver();

        // Create two integer constants x and y
        final ConstDecl<IntType> cx = Const("x", IntExprs.Int());
        final ConstDecl<IntType> cy = Const("y", IntExprs.Int());

        // Add x == y + 1 to the solver
        solver.add(IntExprs.Eq(cx.getRef(), IntExprs.Add(cy.getRef(), IntExprs.Int(1))));

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
        final UCSolver solver = solverFactory.createUCSolver();

        final ConstDecl<BoolType> ca = Const("a", BoolExprs.Bool());
        final Expr<BoolType> expr = BoolExprs.And(ca.getRef(), BoolExprs.True());

        solver.push();
        solver.track(expr);

        final SolverStatus status = solver.check();

        assertTrue(status.isSat());

        solver.pop();
    }

    @Test
    public void testUnsatCore() {
        final UCSolver solver = solverFactory.createUCSolver();

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
    public void testModel() {
        final UCSolver solver = solverFactory.createUCSolver();

        final ConstDecl<IntType> x = Const("x", IntExprs.Int());
        final ConstDecl<IntType> y = Const("y", IntExprs.Int());
        final ConstDecl<IntType> z = Const("z", IntExprs.Int());
        final ConstDecl<BoolType> u = Const("u", BoolExprs.Bool());
        final Expr<BoolType> expr1 = IntExprs.Eq(x.getRef(), IntExprs.Int(2));
        final Expr<BoolType> expr2 = IntExprs.Eq(y.getRef(), IntExprs.Int(3));
        final Expr<BoolType> expr3 = IntExprs.Eq(z.getRef(), IntExprs.Add(x.getRef(), y.getRef()));
        final Expr<BoolType> expr4 = BoolExprs.Iff(u.getRef(), BoolExprs.True());

        solver.track(expr1);
        solver.track(expr2);
        solver.track(expr3);
        solver.track(expr4);

        final SolverStatus status = solver.check();
        assertTrue(status.isSat());

        final var model = solver.getModel();
        assertEquals(IntExprs.Int(2), model.eval(x).orElseThrow());
        assertEquals(IntExprs.Int(3), model.eval(y).orElseThrow());
        assertEquals(IntExprs.Int(5), model.eval(z).orElseThrow());
        assertEquals(BoolExprs.Bool(true), model.eval(u).orElseThrow());
    }

    @Test
    public void testFunc() {
        // Arrange
        final Solver solver = solverFactory.createSolver();
        final ConstDecl<FuncType<IntType, IntType>> ca = Const("a", Func(IntExprs.Int(), IntExprs.Int()));
        final Expr<FuncType<IntType, IntType>> a = ca.getRef();
        final ParamDecl<IntType> px = Param("x", IntExprs.Int());
        final Expr<IntType> x = px.getRef();

        solver.add(BoolExprs.Forall(of(px), BoolExprs.Imply(IntExprs.Leq(x, IntExprs.Int(0)), IntExprs.Eq(App(a, x), IntExprs.Int(0)))));
        solver.add(BoolExprs.Forall(of(px), BoolExprs.Imply(IntExprs.Geq(x, IntExprs.Int(1)), IntExprs.Eq(App(a, x), IntExprs.Int(1)))));

        // Act
        final SolverStatus status = solver.check();
        assertTrue(status.isSat());
        final Valuation model = solver.getModel();
        final Optional<LitExpr<FuncType<IntType, IntType>>> optVal = model.eval(ca);
        final Expr<FuncType<IntType, IntType>> val = optVal.get();

        // Assert
        assertEquals(ca.getType(), val.getType());
    }

    @Test
    public void testArray() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<ArrayType<IntType, IntType>> arr = Const("arr", Array(IntExprs.Int(), IntExprs.Int()));

        solver.add(ArrayExprs.Eq(Write(arr.getRef(), IntExprs.Int(0), IntExprs.Int(1)), arr.getRef()));
        solver.add(ArrayExprs.Eq(Write(arr.getRef(), IntExprs.Int(1), IntExprs.Int(2)), arr.getRef()));

        // Check, the expression should be satisfiable
        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation valuation = solver.getModel();
        final Optional<LitExpr<ArrayType<IntType, IntType>>> optVal = valuation.eval(arr);
        final Expr<ArrayType<IntType, IntType>> val = optVal.get();
        assertTrue(val instanceof ArrayLitExpr);
        var valLit = (ArrayLitExpr<IntType, IntType>)val;
        assertTrue(2 <= valLit.getElements().size());
        assertEquals(IntExprs.Int(1), Read(valLit, IntExprs.Int(0)).eval(ImmutableValuation.empty()));
        assertEquals(IntExprs.Int(2), Read(valLit, IntExprs.Int(1)).eval(ImmutableValuation.empty()));
    }

    @Test
    public void testBV1() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[]{false, false, true, false})));
        solver.add(BvExprs.Eq(cy.getRef(), Bv(new boolean[]{false, false, true, false})));
        solver.add(BvExprs.Eq(cx.getRef(), cy.getRef()));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        solver.pop();
    }

    @Test
    public void testBV2() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cz = Const("z", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[]{false, false, false, false})));
        solver.add(BvExprs.Neq(cx.getRef(), cz.getRef()));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV3() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[] {false, false, false, false})));
        solver.add(BvExprs.Eq(cy.getRef(), BvExprs.Add(List.of(cx.getRef(), Bv(new boolean[] {false, false, false, true})))));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV4() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[] {false, false, true, false})));
        solver.add(BvExprs.Eq(cy.getRef(), BvExprs.Sub(cx.getRef(), Bv(new boolean[] {false, false, false, true}))));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV5() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[] {false, false, true, false})));
        solver.add(BvExprs.Eq(cy.getRef(), BvExprs.Neg(cx.getRef())));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV6() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[] {false, false, true, false})));
        solver.add(BvExprs.Eq(cy.getRef(), BvExprs.Mul(List.of(cx.getRef(), Bv(new boolean[] {false, false, true, false})))));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV7() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.ULt(cx.getRef(), Bv(new boolean[] {true, true, true, true})));
        solver.add(BvExprs.ULt(cy.getRef(), Bv(new boolean[] {true, true, true, true})));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV8() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[] {true, false, true, false})));
        solver.add(BvExprs.Eq(cy.getRef(), BvExprs.SMod(cx.getRef(), Bv(new boolean[] {false, true, false, false}))));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV9() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cy.getRef(), Bv(new boolean[] {false, true, false, false})));
        solver.add(BvExprs.Eq(BvExprs.Or(List.of(cx.getRef(), cy.getRef())), Bv(new boolean[] {true, true, false, false})));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV10() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cy.getRef(), Bv(new boolean[] {false, true, false, false})));
        solver.add(BvExprs.Eq(BvExprs.And(List.of(cx.getRef(), cy.getRef())), Bv(new boolean[] {false, true, false, false})));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV11() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cy.getRef(), Bv(new boolean[] {false, true, false, false})));
        solver.add(BvExprs.Eq(BvExprs.Xor(List.of(cx.getRef(), cy.getRef())), Bv(new boolean[] {false, true, false, false})));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV12() {
        final Solver solver = solverFactory.createSolver();

        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cy.getRef(), Bv(new boolean[] {false, true, false, false})));
        solver.add(BvExprs.Eq(BvExprs.ArithShiftRight(cy.getRef(), Bv(new boolean[] {false, false, false, true})), cx.getRef()));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }
}
