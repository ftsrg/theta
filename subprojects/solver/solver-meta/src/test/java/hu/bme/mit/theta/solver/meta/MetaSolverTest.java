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

package hu.bme.mit.theta.solver.meta;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import org.junit.Before;
import org.junit.Test;

import java.util.List;
import java.util.Optional;

import static com.google.common.collect.ImmutableList.of;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.*;
import static org.junit.Assert.assertNotNull;

public class MetaSolverTest {
    private Solver solver;

    @Before
    public void setup() {
        solver = MetaSolverFactory.getInstance().createSolver();
    }

    @Test
    public void testSimple() {
        // Create two integer constants x and y
        final ConstDecl<IntType> cx = Const("x", Int());
        final ConstDecl<IntType> cy = Const("y", Int());

        // Add x == y + 1 to the solver
        solver.add(Eq(cx.getRef(), Add(cy.getRef(), Int(1))));

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
    public void testFunc() {
        // Arrange
        final ConstDecl<FuncType<IntType, IntType>> ca = Const("a", Func(Int(), Int()));
        final Expr<FuncType<IntType, IntType>> a = ca.getRef();
        final ParamDecl<IntType> px = Param("x", Int());
        final Expr<IntType> x = px.getRef();

        solver.add(
                BoolExprs.Forall(
                        of(px), BoolExprs.Imply(IntExprs.Leq(x, Int(0)), Eq(App(a, x), Int(0)))));
        solver.add(
                BoolExprs.Forall(
                        of(px), BoolExprs.Imply(IntExprs.Geq(x, Int(1)), Eq(App(a, x), Int(1)))));

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
    public void testReset() {
        final ConstDecl<IntType> cx = Const("x", Int());
        final ConstDecl<IntType> cy = Const("y", Int());

        IntEqExpr eqExpr = Eq(cx.getRef(), Add(cy.getRef(), Int(1)));
        solver.add(eqExpr);
        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        solver.add(IntExprs.Lt(cx.getRef(), cy.getRef()));
        status = solver.check();
        assertTrue(status.isUnsat());

        solver.reset();
        assertEquals(0, solver.getAssertions().size());

        solver.add(eqExpr);
        status = solver.check();
        assertTrue(status.isSat());
    }

    @Test(expected = IllegalArgumentException.class)
    public void testResetStack() {
        solver.push();
        solver.push();
        solver.pop();
        solver.reset();
        solver.pop();
    }

    @Test
    public void testBV1() {
        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[] {false, false, true, false})));
        solver.add(BvExprs.Eq(cy.getRef(), Bv(new boolean[] {false, false, true, false})));
        solver.add(BvExprs.Eq(cx.getRef(), cy.getRef()));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        solver.pop();
    }

    @Test
    public void testBV2() {
        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cz = Const("z", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[] {false, false, false, false})));
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
        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[] {false, false, false, false})));
        solver.add(
                BvExprs.Eq(
                        cy.getRef(),
                        BvExprs.Add(
                                List.of(
                                        cx.getRef(),
                                        Bv(new boolean[] {false, false, false, true})))));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV4() {
        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[] {false, false, true, false})));
        solver.add(
                BvExprs.Eq(
                        cy.getRef(),
                        BvExprs.Sub(cx.getRef(), Bv(new boolean[] {false, false, false, true}))));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV5() {
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
        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[] {false, false, true, false})));
        solver.add(
                BvExprs.Eq(
                        cy.getRef(),
                        BvExprs.Mul(
                                List.of(
                                        cx.getRef(),
                                        Bv(new boolean[] {false, false, true, false})))));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV7() {
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
        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cx.getRef(), Bv(new boolean[] {true, false, true, false})));
        solver.add(
                BvExprs.Eq(
                        cy.getRef(),
                        BvExprs.SMod(cx.getRef(), Bv(new boolean[] {false, true, false, false}))));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV9() {
        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cy.getRef(), Bv(new boolean[] {false, true, false, false})));
        solver.add(
                BvExprs.Eq(
                        BvExprs.Or(List.of(cx.getRef(), cy.getRef())),
                        Bv(new boolean[] {true, true, false, false})));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV10() {
        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cy.getRef(), Bv(new boolean[] {false, true, false, false})));
        solver.add(
                BvExprs.Eq(
                        BvExprs.And(List.of(cx.getRef(), cy.getRef())),
                        Bv(new boolean[] {false, true, false, false})));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV11() {
        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cy.getRef(), Bv(new boolean[] {false, true, false, false})));
        solver.add(
                BvExprs.Eq(
                        BvExprs.Xor(List.of(cx.getRef(), cy.getRef())),
                        Bv(new boolean[] {false, true, false, false})));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }

    @Test
    public void testBV12() {
        final ConstDecl<BvType> cx = Const("x", BvExprs.BvType(4));
        final ConstDecl<BvType> cy = Const("y", BvExprs.BvType(4));

        solver.push();

        solver.add(BvExprs.Eq(cy.getRef(), Bv(new boolean[] {false, true, false, false})));
        solver.add(
                BvExprs.Eq(
                        BvExprs.ArithShiftRight(
                                cy.getRef(), Bv(new boolean[] {false, false, false, true})),
                        cx.getRef()));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());

        Valuation model = solver.getModel();
        assertNotNull(model);
        assertNotNull(model.toMap());

        solver.pop();
    }
}
