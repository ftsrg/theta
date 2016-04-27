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

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.impl.Decls;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.model.impl.EmptyModel;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.impl.Types;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprSimplifierVisitor;

public class ExprSimplifierTests {

	private final ExprSimplifierVisitor visitor = new ExprSimplifierVisitor();
	private final ConstDecl<BoolType> cx = Decls.Const("x", Types.Bool());
	private final ConstDecl<IntType> ca = Decls.Const("a", Types.Int());
	private final ConstDecl<IntType> cb = Decls.Const("b", Types.Int());

	@Test
	public void testNot() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				False(),
				Not(And(True(), True())).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Not(And(False(), True())).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testAnd() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				cx.getRef(),
				And(True(), cx.getRef(), True()).accept(visitor, model));
		Assert.assertEquals(
				False(),
				And(True(), cx.getRef(), False()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testOr() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				cx.getRef(),
				Or(False(), cx.getRef(), False()).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Or(False(), cx.getRef(), True()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testImply() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				True(),
				Imply(False(), cx.getRef()).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Imply(cx.getRef(), True()).accept(visitor, model));
		Assert.assertEquals(
				cx.getRef(),
				Imply(True(), cx.getRef()).accept(visitor, model));
		Assert.assertEquals(
				Not(cx.getRef()),
				Imply(cx.getRef(), False()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testIff() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				Not(cx.getRef()),
				Iff(False(), cx.getRef()).accept(visitor, model));
		Assert.assertEquals(
				cx.getRef(),
				Iff(cx.getRef(), True()).accept(visitor, model));
		Assert.assertEquals(
				cx.getRef(),
				Iff(True(), cx.getRef()).accept(visitor, model));
		Assert.assertEquals(
				Not(cx.getRef()),
				Iff(cx.getRef(), False()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testEq() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				True(),
				Eq(False(), False()).accept(visitor, model));
		Assert.assertEquals(
				False(),
				Eq(False(), True()).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Eq(Int(2), Int(2)).accept(visitor, model));
		Assert.assertEquals(
				False(),
				Eq(Int(2), Int(-2)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Eq(Rat(1, 2), Rat(1, 2)).accept(visitor, model));
		Assert.assertEquals(
				False(),
				Eq(Rat(1, 2), Rat(-1, 2)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Eq(ca.getRef(), ca.getRef()).accept(visitor, model));
		Assert.assertEquals(
				Eq(ca.getRef(), cb.getRef()),
				Eq(ca.getRef(), cb.getRef()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testGeq() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				True(),
				Geq(Rat(8, 4), Int(2)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Geq(Rat(3, 4), Rat(2, 3)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Geq(Rat(9, 4), Int(2)).accept(visitor, model));
		Assert.assertEquals(
				False(),
				Geq(Int(2), Rat(9, 4)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Geq(ca.getRef(), ca.getRef()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testGt() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				False(),
				Gt(Rat(8, 4), Int(2)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Gt(Rat(3, 4), Rat(2, 3)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Gt(Rat(9, 4), Int(2)).accept(visitor, model));
		Assert.assertEquals(
				False(),
				Gt(Int(2), Rat(9, 4)).accept(visitor, model));
		Assert.assertEquals(
				False(),
				Gt(ca.getRef(), ca.getRef()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testLeq() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				True(),
				Leq(Rat(8, 4), Int(2)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Leq(Rat(2, 3), Rat(3, 4)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Leq(Int(2), Rat(9, 4)).accept(visitor, model));
		Assert.assertEquals(
				False(),
				Leq(Rat(9, 4), Int(2)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Leq(ca.getRef(), ca.getRef()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testLt() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				False(),
				Lt(Int(2), Rat(8, 4)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Lt(Rat(2, 3), Rat(3, 4)).accept(visitor, model));
		Assert.assertEquals(
				True(),
				Lt(Int(2), Rat(9, 4)).accept(visitor, model));
		Assert.assertEquals(
				False(),
				Lt(Rat(9, 4), Int(2)).accept(visitor, model));
		Assert.assertEquals(
				False(),
				Lt(ca.getRef(), ca.getRef()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testIntDiv() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				Int(0),
				IntDiv(Int(1), Int(2)).accept(visitor, model));
		Assert.assertEquals(
				Int(1),
				IntDiv(Int(3), Int(2)).accept(visitor, model));
		Assert.assertEquals(
				IntDiv(Int(0), ca.getRef()),
				IntDiv(Int(0), ca.getRef()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testRatDiv() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				Rat(8, 9),
				RatDiv(Rat(2, 3), Rat(3, 4)).accept(visitor, model));
		Assert.assertEquals(
				Rat(1, 2),
				RatDiv(Rat(2, 3), Rat(4, 3)).accept(visitor, model));
		Assert.assertEquals(
				Rat(1, 3),
				RatDiv(Rat(2, 3), Int(2)).accept(visitor, model));
		Assert.assertEquals(
				Rat(1, 2),
				RatDiv(Int(2), Int(4)).accept(visitor, model));
		Assert.assertEquals(
				RatDiv(Int(0), ca.getRef()),
				RatDiv(Int(0), ca.getRef()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testNeg() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				Rat(1, 2),
				Neg(Neg(Neg(Neg(Rat(1, 2))))).accept(visitor, model));
		Assert.assertEquals(
				Rat(-1, 2),
				Neg(Neg(Neg(Neg(Neg(Rat(1, 2)))))).accept(visitor, model));
		Assert.assertEquals(
				Int(182),
				Neg(Neg(Neg(Neg(Int(182))))).accept(visitor, model));
		Assert.assertEquals(
				Int(-182),
				Neg(Neg(Neg(Neg(Neg(Int(182)))))).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testSub() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				Int(-1),
				Sub(Int(7), Int(8)).accept(visitor, model));
		Assert.assertEquals(
				Rat(1, 4),
				Sub(Rat(3, 4), Rat(1, 2)).accept(visitor, model));
		Assert.assertEquals(
				Rat(-1, 4),
				Sub(Rat(3, 4), Int(1)).accept(visitor, model));
		Assert.assertEquals(
				Int(0),
				Sub(ca.getRef(), ca.getRef()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testAdd() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				Int(6),
				Add(Int(1), Int(2), Int(3)).accept(visitor, model));
		Assert.assertEquals(
				Int(0),
				Add(Int(1), Int(2), Int(-3)).accept(visitor, model));
		Assert.assertEquals(
				Rat(7, 12),
				Add(Rat(1, 3), Rat(1, 4)).accept(visitor, model));
		Assert.assertEquals(
				Add(ca.getRef(), Int(4)),
				Add(Int(1), ca.getRef(), Int(3)).accept(visitor, model));
		Assert.assertEquals(
				ca.getRef(),
				Add(Int(-3), ca.getRef(), Int(3)).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testMul() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				Int(30),
				Mul(Int(2), Int(3), Int(5)).accept(visitor, model));
		Assert.assertEquals(
				Mul(Int(10), ca.getRef()),
				Mul(Int(2), ca.getRef(), Int(5)).accept(visitor, model));
		Assert.assertEquals(
				Int(0),
				Mul(Int(0), ca.getRef(), cb.getRef()).accept(visitor, model));
		Assert.assertEquals(
				Int(1),
				Mul(Int(2), Int(1), Rat(1, 2)).accept(visitor, model));
		Assert.assertEquals(
				ca.getRef(),
				Mul(Int(2), ca.getRef(), Rat(1, 2)).accept(visitor, model));
		Assert.assertEquals(
				Rat(3, 4),
				Mul(Rat(3, 2), Int(1), Rat(1, 2)).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testIte() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				ca.getRef(),
				Ite(True(), ca.getRef(), cb.getRef()).accept(visitor, model));
		Assert.assertEquals(
				cb.getRef(),
				Ite(False(), ca.getRef(), cb.getRef()).accept(visitor, model));
		Assert.assertEquals(
				ca.getRef(),
				Ite(True(), Ite(True(), Ite(True(), ca.getRef(), cb.getRef()), cb.getRef()), cb.getRef()).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testComplex() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				True(),
				Eq(And(cx.getRef(), True()), Or(cx.getRef(), False())).accept(visitor, model));
		//@formatter:on
	}
}
