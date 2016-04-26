package hu.bme.mit.inf.ttmc.core.tests;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.impl.Decls;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.model.impl.EmptyModel;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.impl.Types;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprSimplifierVisitor;

public class ExprSimplifierTests {

	private final ExprSimplifierVisitor visitor = new ExprSimplifierVisitor();
	private final ConstDecl<BoolType> cx = Decls.Const("x", Types.Bool());
	private final ConstDecl<BoolType> cy = Decls.Const("y", Types.Bool());
	private final ConstDecl<IntType> ca = Decls.Const("a", Types.Int());
	//private final ConstDecl<IntType> cb = Decls.Const("b", Types.Int());
	//private final ConstDecl<IntType> cc = Decls.Const("c", Types.Int());

	@Test
	public void testBoolean() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				Exprs.False(),
				Exprs.Not(Exprs.And(Exprs.True(), Exprs.True())).accept(visitor, model));
		Assert.assertEquals(
				Exprs.True(),
				Exprs.Not(Exprs.And(Exprs.False(), Exprs.True())).accept(visitor, model));
		Assert.assertEquals(
				Exprs.True(),
				Exprs.Imply(Exprs.False(), Exprs.True()).accept(visitor, model));
		Assert.assertEquals(
				cx.getRef(),
				Exprs.And(Exprs.True(), cx.getRef(), Exprs.True()).accept(visitor, model));
		Assert.assertEquals(
				cx.getRef(),
				Exprs.Or(Exprs.False(), cx.getRef(), Exprs.False()).accept(visitor, model));
		Assert.assertEquals(
				Exprs.True(),
				Exprs.Iff(Exprs.And(cx.getRef(), cy.getRef()), Exprs.And(cy.getRef(), cx.getRef())).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testEq() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				Exprs.True(),
				Exprs.Eq(Exprs.And(cx.getRef(), Exprs.True()), Exprs.Or(cx.getRef(), Exprs.False())).accept(visitor, model));
		Assert.assertEquals(
				Exprs.True(),
				Exprs.Eq(Exprs.Rat(8, 4), Exprs.Int(2)).accept(visitor, model));
		//@formatter:on
	}

	@Test
	public void testComparators() {
		final Model model = new EmptyModel();

		//@formatter:off
		Assert.assertEquals(
				Exprs.True(),
				Exprs.Geq(Exprs.Rat(3, 4), Exprs.Rat(2, 3)).accept(visitor, model));
		Assert.assertEquals(
				Exprs.True(),
				Exprs.Geq(Exprs.Rat(9, 4), Exprs.Int(2)).accept(visitor, model));
		Assert.assertEquals(
				Exprs.True(),
				Exprs.Geq(ca.getRef(), ca.getRef()).accept(visitor, model));
		//@formatter:on
	}
}
