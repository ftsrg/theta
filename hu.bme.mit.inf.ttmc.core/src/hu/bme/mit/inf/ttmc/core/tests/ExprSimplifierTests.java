package hu.bme.mit.inf.ttmc.core.tests;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Add;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.False;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Gt;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Iff;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.IntDiv;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Ite;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Lt;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Mul;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Neg;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Rat;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.RatDiv;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Sub;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.True;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils.simplify;

import java.util.HashMap;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.impl.Decls;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.model.impl.BasicModel;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;

public class ExprSimplifierTests {

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
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(False(), simplify(Not(And(True(), True())), model));
		Assert.assertEquals(True(), simplify(Not(And(False(), True())), model));
		// @formatter:on
	}

	@Test
	public void testAnd() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(x, simplify(And(True(), x, True()), model));
		Assert.assertEquals(False(), simplify(And(True(), x, False()), model));
		Assert.assertEquals(And(x, y, z), simplify(And(x, And(y, z)), model));
		// @formatter:on
	}

	@Test
	public void testOr() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(x, simplify(Or(False(), x, False()), model));
		Assert.assertEquals(True(), simplify(Or(False(), x, True()), model));
		// @formatter:on
	}

	@Test
	public void testImply() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(True(), simplify(Imply(False(), x), model));
		Assert.assertEquals(True(), simplify(Imply(x, True()), model));
		Assert.assertEquals(x, simplify(Imply(True(), x), model));
		Assert.assertEquals(Not(x), simplify(Imply(x, False()), model));
		// @formatter:on
	}

	@Test
	public void testIff() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(Not(x), simplify(Iff(False(), x), model));
		Assert.assertEquals(x, simplify(Iff(x, True()), model));
		Assert.assertEquals(x, simplify(Iff(True(), x), model));
		Assert.assertEquals(Not(x), simplify(Iff(x, False()), model));
		// @formatter:on
	}

	@Test
	public void testEq() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(True(), simplify(Eq(False(), False()), model));
		Assert.assertEquals(False(), simplify(Eq(False(), True()), model));
		Assert.assertEquals(True(), simplify(Eq(Int(2), Int(2)), model));
		Assert.assertEquals(False(), simplify(Eq(Int(2), Int(-2)), model));
		Assert.assertEquals(True(), simplify(Eq(Rat(1, 2), Rat(1, 2)), model));
		Assert.assertEquals(False(), simplify(Eq(Rat(1, 2), Rat(-1, 2)), model));
		Assert.assertEquals(True(), simplify(Eq(a, a), model));
		Assert.assertEquals(Eq(a, b), simplify(Eq(a, b), model));
		// @formatter:on
	}

	@Test
	public void testGeq() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(True(), simplify(Geq(Rat(8, 4), Int(2)), model));
		Assert.assertEquals(True(), simplify(Geq(Rat(3, 4), Rat(2, 3)), model));
		Assert.assertEquals(True(), simplify(Geq(Rat(9, 4), Int(2)), model));
		Assert.assertEquals(False(), simplify(Geq(Int(2), Rat(9, 4)), model));
		Assert.assertEquals(True(), simplify(Geq(a, a), model));
		// @formatter:on
	}

	@Test
	public void testGt() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(False(), simplify(Gt(Rat(8, 4), Int(2)), model));
		Assert.assertEquals(True(), simplify(Gt(Rat(3, 4), Rat(2, 3)), model));
		Assert.assertEquals(True(), simplify(Gt(Rat(9, 4), Int(2)), model));
		Assert.assertEquals(False(), simplify(Gt(Int(2), Rat(9, 4)), model));
		Assert.assertEquals(False(), simplify(Gt(a, a), model));
		// @formatter:on
	}

	@Test
	public void testLeq() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(True(), simplify(Leq(Rat(8, 4), Int(2)), model));
		Assert.assertEquals(True(), simplify(Leq(Rat(2, 3), Rat(3, 4)), model));
		Assert.assertEquals(True(), simplify(Leq(Int(2), Rat(9, 4)), model));
		Assert.assertEquals(False(), simplify(Leq(Rat(9, 4), Int(2)), model));
		Assert.assertEquals(True(), simplify(Leq(a, a), model));
		// @formatter:on
	}

	@Test
	public void testLt() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(False(), simplify(Lt(Int(2), Rat(8, 4)), model));
		Assert.assertEquals(True(), simplify(Lt(Rat(2, 3), Rat(3, 4)), model));
		Assert.assertEquals(True(), simplify(Lt(Int(2), Rat(9, 4)), model));
		Assert.assertEquals(False(), simplify(Lt(Rat(9, 4), Int(2)), model));
		Assert.assertEquals(False(), simplify(Lt(a, a), model));
		// @formatter:on
	}

	@Test
	public void testIntDiv() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(Int(0), simplify(IntDiv(Int(1), Int(2)), model));
		Assert.assertEquals(Int(1), simplify(IntDiv(Int(3), Int(2)), model));
		Assert.assertEquals(IntDiv(Int(0), a), simplify(IntDiv(Int(0), a), model));
		// @formatter:on
	}

	@Test
	public void testRatDiv() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(Rat(8, 9), simplify(RatDiv(Rat(2, 3), Rat(3, 4)), model));
		Assert.assertEquals(Rat(1, 2), simplify(RatDiv(Rat(2, 3), Rat(4, 3)), model));
		Assert.assertEquals(Rat(1, 3), simplify(RatDiv(Rat(2, 3), Int(2)), model));
		Assert.assertEquals(Rat(1, 2), simplify(RatDiv(Int(2), Int(4)), model));
		Assert.assertEquals(RatDiv(Int(0), a), simplify(RatDiv(Int(0), a), model));
		// @formatter:on
	}

	@Test
	public void testNeg() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(Rat(1, 2), simplify(Neg(Neg(Neg(Neg(Rat(1, 2))))), model));
		Assert.assertEquals(Rat(-1, 2), simplify(Neg(Neg(Neg(Neg(Neg(Rat(1, 2)))))), model));
		Assert.assertEquals(Int(182), simplify(Neg(Neg(Neg(Neg(Int(182))))), model));
		Assert.assertEquals(Int(-182), simplify(Neg(Neg(Neg(Neg(Neg(Int(182)))))), model));
		// @formatter:on
	}

	@Test
	public void testSub() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(Int(-1), simplify(Sub(Int(7), Int(8)), model));
		Assert.assertEquals(Rat(1, 4), simplify(Sub(Rat(3, 4), Rat(1, 2)), model));
		Assert.assertEquals(Rat(-1, 4), simplify(Sub(Rat(3, 4), Int(1)), model));
		Assert.assertEquals(Int(0), simplify(Sub(a, a), model));
		// @formatter:on
	}

	@Test
	public void testAdd() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(Int(6), simplify(Add(Int(1), Int(2), Int(3)), model));
		Assert.assertEquals(Int(0), simplify(Add(Int(1), Int(2), Int(-3)), model));
		Assert.assertEquals(Rat(7, 12), simplify(Add(Rat(1, 3), Rat(1, 4)), model));
		Assert.assertEquals(Add(a, Int(4)), simplify(Add(Int(1), a, Int(3)), model));
		Assert.assertEquals(a, simplify(Add(Int(-3), a, Int(3)), model));
		Assert.assertEquals(Add(a, b, a, b, c), simplify(Add(a, Add(b, Add(a, Add(b, c)))), model));
		// @formatter:on
	}

	@Test
	public void testMul() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(Int(30), simplify(Mul(Int(2), Int(3), Int(5)), model));
		Assert.assertEquals(Mul(Int(10), a), simplify(Mul(Int(2), a, Int(5)), model));
		Assert.assertEquals(Int(0), simplify(Mul(Int(0), a, b), model));
		Assert.assertEquals(Int(1), simplify(Mul(Int(2), Int(1), Rat(1, 2)), model));
		Assert.assertEquals(a, simplify(Mul(Int(2), a, Rat(1, 2)), model));
		Assert.assertEquals(Rat(3, 4), simplify(Mul(Rat(3, 2), Int(1), Rat(1, 2)), model));
		Assert.assertEquals(Mul(a, b, a, b, c), simplify(Mul(a, Mul(b, Mul(a, Mul(b, c)))), model));
		// @formatter:on
	}

	@Test
	public void testIte() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(a, simplify(Ite(True(), a, b), model));
		Assert.assertEquals(b, simplify(Ite(False(), a, b), model));
		Assert.assertEquals(a, simplify(Ite(True(), Ite(True(), Ite(True(), a, b), b), b), model));
		// @formatter:on
	}

	@Test
	public void testComplex() {
		final Model model = new BasicModel();

		// @formatter:off
		Assert.assertEquals(True(), simplify(Eq(And(x, True()), Or(x, False())), model));
		// @formatter:on
	}

	@Test
	public void testModel() {
		final Map<ConstDecl<?>, LitExpr<?>> constToExpr = new HashMap<>();
		constToExpr.put(ca, Int(5));
		constToExpr.put(cb, Int(9));
		final Model model = new BasicModel(constToExpr);

		// @formatter:off
		Assert.assertEquals(Int(14), simplify(Add(a, b), model));
		Assert.assertEquals(Add(Int(14), c), simplify(Add(a, b, c), model));
		// @formatter:on
	}
}
