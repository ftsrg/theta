package hu.bme.mit.inf.theta.core.utils;

import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Add;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.False;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Gt;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Iff;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.IntDiv;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Ite;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Lt;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Mul;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Neg;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Rat;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.RatDiv;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Sub;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.True;
import static hu.bme.mit.inf.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.theta.core.type.impl.Types.Int;
import static hu.bme.mit.inf.theta.core.utils.impl.ExprUtils.simplify;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.inf.theta.core.decl.ConstDecl;
import hu.bme.mit.inf.theta.core.decl.Decl;
import hu.bme.mit.inf.theta.core.decl.impl.Decls;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.LitExpr;
import hu.bme.mit.inf.theta.core.model.Assignment;
import hu.bme.mit.inf.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.IntType;

public class ExprSimplifierTest {

	private final ConstDecl<BoolType> cx = Decls.Const("x", Bool());
	private final ConstDecl<BoolType> cy = Decls.Const("y", Bool());
	private final ConstDecl<BoolType> cz = Decls.Const("z", Bool());
	private final ConstDecl<IntType> ca = Decls.Const("a", Int());
	private final ConstDecl<IntType> cb = Decls.Const("b", Int());
	private final ConstDecl<IntType> cc = Decls.Const("c", Int());

	private final Expr<BoolType> x = cx.getRef();
	private final Expr<BoolType> y = cy.getRef();
	private final Expr<BoolType> z = cz.getRef();
	private final Expr<IntType> a = ca.getRef();
	private final Expr<IntType> b = cb.getRef();
	private final Expr<IntType> c = cc.getRef();

	@Test
	public void testNot() {
		// @formatter:off
		Assert.assertEquals(False(), simplify(Not(And(True(), True()))));
		Assert.assertEquals(True(), simplify(Not(And(False(), True()))));
		Assert.assertEquals(True(), simplify(And(Collections.emptySet())));
		// @formatter:on
	}

	@Test
	public void testAnd() {
		// @formatter:off
		Assert.assertEquals(x, simplify(And(True(), x, True())));
		Assert.assertEquals(False(), simplify(And(True(), x, False())));
		Assert.assertEquals(And(x, y, z), simplify(And(x, And(y, z))));
		Assert.assertEquals(True(), simplify(And(Collections.emptySet())));
		// @formatter:on
	}

	@Test
	public void testOr() {
		// @formatter:off
		Assert.assertEquals(x, simplify(Or(False(), x, False())));
		Assert.assertEquals(True(), simplify(Or(False(), x, True())));
		// @formatter:on
	}

	@Test
	public void testImply() {
		// @formatter:off
		Assert.assertEquals(True(), simplify(Imply(False(), x)));
		Assert.assertEquals(True(), simplify(Imply(x, True())));
		Assert.assertEquals(x, simplify(Imply(True(), x)));
		Assert.assertEquals(Not(x), simplify(Imply(x, False())));
		// @formatter:on
	}

	@Test
	public void testIff() {
		// @formatter:off
		Assert.assertEquals(Not(x), simplify(Iff(False(), x)));
		Assert.assertEquals(x, simplify(Iff(x, True())));
		Assert.assertEquals(x, simplify(Iff(True(), x)));
		Assert.assertEquals(Not(x), simplify(Iff(x, False())));
		// @formatter:on
	}

	@Test
	public void testEq() {
		// @formatter:off
		Assert.assertEquals(True(), simplify(Eq(False(), False())));
		Assert.assertEquals(False(), simplify(Eq(False(), True())));
		Assert.assertEquals(True(), simplify(Eq(Int(2), Int(2))));
		Assert.assertEquals(False(), simplify(Eq(Int(2), Int(-2))));
		Assert.assertEquals(True(), simplify(Eq(Rat(1, 2), Rat(1, 2))));
		Assert.assertEquals(False(), simplify(Eq(Rat(1, 2), Rat(-1, 2))));
		Assert.assertEquals(True(), simplify(Eq(a, a)));
		Assert.assertEquals(Eq(a, b), simplify(Eq(a, b)));
		// @formatter:on
	}

	@Test
	public void testGeq() {
		// @formatter:off
		Assert.assertEquals(True(), simplify(Geq(Rat(8, 4), Int(2))));
		Assert.assertEquals(True(), simplify(Geq(Rat(3, 4), Rat(2, 3))));
		Assert.assertEquals(True(), simplify(Geq(Rat(9, 4), Int(2))));
		Assert.assertEquals(False(), simplify(Geq(Int(2), Rat(9, 4))));
		Assert.assertEquals(True(), simplify(Geq(a, a)));
		// @formatter:on
	}

	@Test
	public void testGt() {
		// @formatter:off
		Assert.assertEquals(False(), simplify(Gt(Rat(8, 4), Int(2))));
		Assert.assertEquals(True(), simplify(Gt(Rat(3, 4), Rat(2, 3))));
		Assert.assertEquals(True(), simplify(Gt(Rat(9, 4), Int(2))));
		Assert.assertEquals(False(), simplify(Gt(Int(2), Rat(9, 4))));
		Assert.assertEquals(False(), simplify(Gt(a, a)));
		// @formatter:on
	}

	@Test
	public void testLeq() {
		// @formatter:off
		Assert.assertEquals(True(), simplify(Leq(Rat(8, 4), Int(2))));
		Assert.assertEquals(True(), simplify(Leq(Rat(2, 3), Rat(3, 4))));
		Assert.assertEquals(True(), simplify(Leq(Int(2), Rat(9, 4))));
		Assert.assertEquals(False(), simplify(Leq(Rat(9, 4), Int(2))));
		Assert.assertEquals(True(), simplify(Leq(a, a)));
		// @formatter:on
	}

	@Test
	public void testLt() {
		// @formatter:off
		Assert.assertEquals(False(), simplify(Lt(Int(2), Rat(8, 4))));
		Assert.assertEquals(True(), simplify(Lt(Rat(2, 3), Rat(3, 4))));
		Assert.assertEquals(True(), simplify(Lt(Int(2), Rat(9, 4))));
		Assert.assertEquals(False(), simplify(Lt(Rat(9, 4), Int(2))));
		Assert.assertEquals(False(), simplify(Lt(a, a)));
		// @formatter:on
	}

	@Test
	public void testIntDiv() {
		// @formatter:off
		Assert.assertEquals(Int(0), simplify(IntDiv(Int(1), Int(2))));
		Assert.assertEquals(Int(1), simplify(IntDiv(Int(3), Int(2))));
		Assert.assertEquals(IntDiv(Int(0), a), simplify(IntDiv(Int(0), a)));
		// @formatter:on
	}

	@Test
	public void testRatDiv() {
		// @formatter:off
		Assert.assertEquals(Rat(8, 9), simplify(RatDiv(Rat(2, 3), Rat(3, 4))));
		Assert.assertEquals(Rat(1, 2), simplify(RatDiv(Rat(2, 3), Rat(4, 3))));
		Assert.assertEquals(Rat(1, 3), simplify(RatDiv(Rat(2, 3), Int(2))));
		Assert.assertEquals(Rat(1, 2), simplify(RatDiv(Int(2), Int(4))));
		Assert.assertEquals(RatDiv(Int(0), a), simplify(RatDiv(Int(0), a)));
		// @formatter:on
	}

	@Test
	public void testNeg() {
		// @formatter:off
		Assert.assertEquals(Rat(1, 2), simplify(Neg(Neg(Neg(Neg(Rat(1, 2)))))));
		Assert.assertEquals(Rat(-1, 2), simplify(Neg(Neg(Neg(Neg(Neg(Rat(1, 2))))))));
		Assert.assertEquals(Int(182), simplify(Neg(Neg(Neg(Neg(Int(182)))))));
		Assert.assertEquals(Int(-182), simplify(Neg(Neg(Neg(Neg(Neg(Int(182))))))));
		// @formatter:on
	}

	@Test
	public void testSub() {
		// @formatter:off
		Assert.assertEquals(Int(-1), simplify(Sub(Int(7), Int(8))));
		Assert.assertEquals(Rat(1, 4), simplify(Sub(Rat(3, 4), Rat(1, 2))));
		Assert.assertEquals(Rat(-1, 4), simplify(Sub(Rat(3, 4), Int(1))));
		Assert.assertEquals(Int(0), simplify(Sub(a, a)));
		// @formatter:on
	}

	@Test
	public void testAdd() {
		// @formatter:off
		Assert.assertEquals(Int(6), simplify(Add(Int(1), Int(2), Int(3))));
		Assert.assertEquals(Int(0), simplify(Add(Int(1), Int(2), Int(-3))));
		Assert.assertEquals(Rat(7, 12), simplify(Add(Rat(1, 3), Rat(1, 4))));
		Assert.assertEquals(Add(a, Int(4)), simplify(Add(Int(1), a, Int(3))));
		Assert.assertEquals(a, simplify(Add(Int(-3), a, Int(3))));
		Assert.assertEquals(Add(a, b, a, b, c), simplify(Add(a, Add(b, Add(a, Add(b, c))))));
		// @formatter:on
	}

	@Test
	public void testMul() {
		// @formatter:off
		Assert.assertEquals(Int(30), simplify(Mul(Int(2), Int(3), Int(5))));
		Assert.assertEquals(Mul(Int(10), a), simplify(Mul(Int(2), a, Int(5))));
		Assert.assertEquals(Int(0), simplify(Mul(Int(0), a, b)));
		Assert.assertEquals(Int(1), simplify(Mul(Int(2), Int(1), Rat(1, 2))));
		Assert.assertEquals(a, simplify(Mul(Int(2), a, Rat(1, 2))));
		Assert.assertEquals(Rat(3, 4), simplify(Mul(Rat(3, 2), Int(1), Rat(1, 2))));
		Assert.assertEquals(Mul(a, b, a, b, c), simplify(Mul(a, Mul(b, Mul(a, Mul(b, c))))));
		// @formatter:on
	}

	@Test
	public void testIte() {
		// @formatter:off
		Assert.assertEquals(a, simplify(Ite(True(), a, b)));
		Assert.assertEquals(b, simplify(Ite(False(), a, b)));
		Assert.assertEquals(a, simplify(Ite(True(), Ite(True(), Ite(True(), a, b), b), b)));
		// @formatter:on
	}

	@Test
	public void testComplex() {
		// @formatter:off
		Assert.assertEquals(True(), simplify(Eq(And(x, True()), Or(x, False()))));
		// @formatter:on
	}

	@Test
	public void testModel() {
		final Map<Decl<?, ?>, LitExpr<?>> declToExpr = new HashMap<>();
		declToExpr.put(ca, Int(5));
		declToExpr.put(cb, Int(9));
		final Assignment assignment = new AssignmentImpl(declToExpr);

		// @formatter:off
		Assert.assertEquals(Int(14), simplify(Add(a, b), assignment));
		Assert.assertEquals(Add(Int(14), c), simplify(Add(a, b, c), assignment));
		// @formatter:on
	}
}
