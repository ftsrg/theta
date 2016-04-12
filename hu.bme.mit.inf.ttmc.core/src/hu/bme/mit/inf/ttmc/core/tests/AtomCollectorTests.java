package hu.bme.mit.inf.ttmc.core.tests;

import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.ConstraintManager;
import hu.bme.mit.inf.ttmc.core.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;

public class AtomCollectorTests {

	@SuppressWarnings("serial")
	@Test
	public void test() {
		final Set<Expr<? extends BoolType>> atoms = new HashSet<>();
		final ConstraintManager manager = new ConstraintManagerImpl();
		final ExprFactory ef = manager.getExprFactory();
		final ConstRefExpr<BoolType> ca = manager.getDeclFactory().Const("a", manager.getTypeFactory().Bool()).getRef();
		final ConstRefExpr<BoolType> cb = manager.getDeclFactory().Const("b", manager.getTypeFactory().Bool()).getRef();
		final ConstRefExpr<IntType> cx = manager.getDeclFactory().Const("x", manager.getTypeFactory().Int()).getRef();
		final ConstRefExpr<IntType> cy = manager.getDeclFactory().Const("y", manager.getTypeFactory().Int()).getRef();

		ExprUtils.collectAtoms(ef.And(ImmutableSet.of(ca, ef.Or(ImmutableSet.of(ca, ef.Not(cb))))), atoms);
		Assert.assertEquals(new HashSet<Expr<? extends Type>>() {
			{
				add(ca);
				add(cb);
			}
		}, atoms);

		atoms.clear();
		ExprUtils.collectAtoms(ef.Imply(ef.Eq(cx, ef.Int(2)), ef.Not(ef.Leq(cx, cy))), atoms);
		Assert.assertEquals(new HashSet<Expr<? extends Type>>() {
			{
				add(ef.Eq(cx, ef.Int(2)));
				add(ef.Leq(cx, cy));
			}
		}, atoms);
	}

}
