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

import java.util.HashMap;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.impl.Decls;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.model.impl.BasicModel;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.impl.Types;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;

public class ExprSimplifierTests {

	private final ConstDecl<BoolType> cx = Decls.Const("x", Types.Bool());
	private final ConstDecl<BoolType> cy = Decls.Const("y", Types.Bool());
	private final ConstDecl<BoolType> cz = Decls.Const("z", Types.Bool());
	private final ConstDecl<IntType> ca = Decls.Const("a", Types.Int());
	private final ConstDecl<IntType> cb = Decls.Const("b", Types.Int());
	private final ConstDecl<IntType> cc = Decls.Const("c", Types.Int());

	@Test
	public void testNot() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Not(And(True(), True())), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Not(And(False(), True())), model));
		//@formatter:on
	}

	@Test
	public void testAnd() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				cx.getRef(),
				ExprUtils.simplify(And(True(), cx.getRef(), True()), model));
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(And(True(), cx.getRef(), False()), model));
		Assert.assertEquals(
				And(cx.getRef(), cy.getRef(), cz.getRef()),
				ExprUtils.simplify(And(cx.getRef(), And(cy.getRef(), cz.getRef())), model));
		//@formatter:on
	}

	@Test
	public void testOr() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				cx.getRef(),
				ExprUtils.simplify(Or(False(), cx.getRef(), False()), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Or(False(), cx.getRef(), True()), model));
		//@formatter:on
	}

	@Test
	public void testImply() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Imply(False(), cx.getRef()), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Imply(cx.getRef(), True()), model));
		Assert.assertEquals(
				cx.getRef(),
				ExprUtils.simplify(Imply(True(), cx.getRef()), model));
		Assert.assertEquals(
				Not(cx.getRef()),
				ExprUtils.simplify(Imply(cx.getRef(), False()), model));
		//@formatter:on
	}

	@Test
	public void testIff() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				Not(cx.getRef()),
				ExprUtils.simplify(Iff(False(), cx.getRef()), model));
		Assert.assertEquals(
				cx.getRef(),
				ExprUtils.simplify(Iff(cx.getRef(), True()), model));
		Assert.assertEquals(
				cx.getRef(),
				ExprUtils.simplify(Iff(True(), cx.getRef()), model));
		Assert.assertEquals(
				Not(cx.getRef()),
				ExprUtils.simplify(Iff(cx.getRef(), False()), model));
		//@formatter:on
	}

	@Test
	public void testEq() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Eq(False(), False()), model));
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Eq(False(), True()), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Eq(Int(2), Int(2)), model));
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Eq(Int(2), Int(-2)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Eq(Rat(1, 2), Rat(1, 2)), model));
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Eq(Rat(1, 2), Rat(-1, 2)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Eq(ca.getRef(), ca.getRef()), model));
		Assert.assertEquals(
				Eq(ca.getRef(), cb.getRef()),
				ExprUtils.simplify(Eq(ca.getRef(), cb.getRef()), model));
		//@formatter:on
	}

	@Test
	public void testGeq() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Geq(Rat(8, 4), Int(2)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Geq(Rat(3, 4), Rat(2, 3)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Geq(Rat(9, 4), Int(2)), model));
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Geq(Int(2), Rat(9, 4)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Geq(ca.getRef(), ca.getRef()), model));
		//@formatter:on
	}

	@Test
	public void testGt() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Gt(Rat(8, 4), Int(2)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Gt(Rat(3, 4), Rat(2, 3)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Gt(Rat(9, 4), Int(2)), model));
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Gt(Int(2), Rat(9, 4)), model));
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Gt(ca.getRef(), ca.getRef()), model));
		//@formatter:on
	}

	@Test
	public void testLeq() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Leq(Rat(8, 4), Int(2)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Leq(Rat(2, 3), Rat(3, 4)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Leq(Int(2), Rat(9, 4)), model));
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Leq(Rat(9, 4), Int(2)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Leq(ca.getRef(), ca.getRef()), model));
		//@formatter:on
	}

	@Test
	public void testLt() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Lt(Int(2), Rat(8, 4)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Lt(Rat(2, 3), Rat(3, 4)), model));
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Lt(Int(2), Rat(9, 4)), model));
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Lt(Rat(9, 4), Int(2)), model));
		Assert.assertEquals(
				False(),
				ExprUtils.simplify(Lt(ca.getRef(), ca.getRef()), model));
		//@formatter:on
	}

	@Test
	public void testIntDiv() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				Int(0),
				ExprUtils.simplify(IntDiv(Int(1), Int(2)), model));
		Assert.assertEquals(
				Int(1),
				ExprUtils.simplify(IntDiv(Int(3), Int(2)), model));
		Assert.assertEquals(
				IntDiv(Int(0), ca.getRef()),
				ExprUtils.simplify(IntDiv(Int(0), ca.getRef()), model));
		//@formatter:on
	}

	@Test
	public void testRatDiv() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				Rat(8, 9),
				ExprUtils.simplify(RatDiv(Rat(2, 3), Rat(3, 4)), model));
		Assert.assertEquals(
				Rat(1, 2),
				ExprUtils.simplify(RatDiv(Rat(2, 3), Rat(4, 3)), model));
		Assert.assertEquals(
				Rat(1, 3),
				ExprUtils.simplify(RatDiv(Rat(2, 3), Int(2)), model));
		Assert.assertEquals(
				Rat(1, 2),
				ExprUtils.simplify(RatDiv(Int(2), Int(4)), model));
		Assert.assertEquals(
				RatDiv(Int(0), ca.getRef()),
				ExprUtils.simplify(RatDiv(Int(0), ca.getRef()), model));
		//@formatter:on
	}

	@Test
	public void testNeg() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				Rat(1, 2),
				ExprUtils.simplify(Neg(Neg(Neg(Neg(Rat(1, 2))))), model));
		Assert.assertEquals(
				Rat(-1, 2),
				ExprUtils.simplify(Neg(Neg(Neg(Neg(Neg(Rat(1, 2)))))), model));
		Assert.assertEquals(
				Int(182),
				ExprUtils.simplify(Neg(Neg(Neg(Neg(Int(182))))), model));
		Assert.assertEquals(
				Int(-182),
				ExprUtils.simplify(Neg(Neg(Neg(Neg(Neg(Int(182)))))), model));
		//@formatter:on
	}

	@Test
	public void testSub() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				Int(-1),
				ExprUtils.simplify(Sub(Int(7), Int(8)), model));
		Assert.assertEquals(
				Rat(1, 4),
				ExprUtils.simplify(Sub(Rat(3, 4), Rat(1, 2)), model));
		Assert.assertEquals(
				Rat(-1, 4),
				ExprUtils.simplify(Sub(Rat(3, 4), Int(1)), model));
		Assert.assertEquals(
				Int(0),
				ExprUtils.simplify(Sub(ca.getRef(), ca.getRef()), model));
		//@formatter:on
	}

	@Test
	public void testAdd() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				Int(6),
				ExprUtils.simplify(Add(Int(1), Int(2), Int(3)), model));
		Assert.assertEquals(
				Int(0),
				ExprUtils.simplify(Add(Int(1), Int(2), Int(-3)), model));
		Assert.assertEquals(
				Rat(7, 12),
				ExprUtils.simplify(Add(Rat(1, 3), Rat(1, 4)), model));
		Assert.assertEquals(
				Add(ca.getRef(), Int(4)),
				ExprUtils.simplify(Add(Int(1), ca.getRef(), Int(3)), model));
		Assert.assertEquals(
				ca.getRef(),
				ExprUtils.simplify(Add(Int(-3), ca.getRef(), Int(3)), model));
		Assert.assertEquals(
				Add(ca.getRef(), cb.getRef(), ca.getRef(), cb.getRef(), cc.getRef()),
				ExprUtils.simplify(Add(ca.getRef(), Add(cb.getRef(), Add(ca.getRef(), Add(cb.getRef(), cc.getRef())))), model));
		//@formatter:on
	}

	@Test
	public void testMul() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				Int(30),
				ExprUtils.simplify(Mul(Int(2), Int(3), Int(5)), model));
		Assert.assertEquals(
				Mul(Int(10), ca.getRef()),
				ExprUtils.simplify(Mul(Int(2), ca.getRef(), Int(5)), model));
		Assert.assertEquals(
				Int(0),
				ExprUtils.simplify(Mul(Int(0), ca.getRef(), cb.getRef()), model));
		Assert.assertEquals(
				Int(1),
				ExprUtils.simplify(Mul(Int(2), Int(1), Rat(1, 2)), model));
		Assert.assertEquals(
				ca.getRef(),
				ExprUtils.simplify(Mul(Int(2), ca.getRef(), Rat(1, 2)), model));
		Assert.assertEquals(
				Rat(3, 4),
				ExprUtils.simplify(Mul(Rat(3, 2), Int(1), Rat(1, 2)), model));
		Assert.assertEquals(
				Mul(ca.getRef(), cb.getRef(), ca.getRef(), cb.getRef(), cc.getRef()),
				ExprUtils.simplify(Mul(ca.getRef(), Mul(cb.getRef(), Mul(ca.getRef(), Mul(cb.getRef(), cc.getRef())))), model));
		//@formatter:on
	}

	@Test
	public void testIte() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				ca.getRef(),
				ExprUtils.simplify(Ite(True(), ca.getRef(), cb.getRef()), model));
		Assert.assertEquals(
				cb.getRef(),
				ExprUtils.simplify(Ite(False(), ca.getRef(), cb.getRef()), model));
		Assert.assertEquals(
				ca.getRef(),
				ExprUtils.simplify(Ite(True(), Ite(True(), Ite(True(), ca.getRef(), cb.getRef()), cb.getRef()), cb.getRef()), model));
		//@formatter:on
	}

	@Test
	public void testComplex() {
		final Model model = new BasicModel();

		//@formatter:off
		Assert.assertEquals(
				True(),
				ExprUtils.simplify(Eq(And(cx.getRef(), True()), Or(cx.getRef(), False())), model));
		//@formatter:on
	}

	@Test
	public void testModel() {
		final Map<ConstDecl<?>, Expr<?>> constToExpr = new HashMap<>();
		constToExpr.put(ca, Int(5));
		constToExpr.put(cb, Int(9));
		final Model model = new BasicModel(constToExpr);

		//@formatter:off
		Assert.assertEquals(
				Int(14),
				ExprUtils.simplify(Add(ca.getRef(), cb.getRef()), model));
		Assert.assertEquals(
				Add(Int(14), cc.getRef()),
				ExprUtils.simplify(Add(ca.getRef(), cb.getRef(), cc.getRef()), model));
		//@formatter:on
	}
}
