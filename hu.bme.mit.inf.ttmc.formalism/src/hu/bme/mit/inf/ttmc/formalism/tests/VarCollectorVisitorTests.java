package hu.bme.mit.inf.ttmc.formalism.tests;

import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

public class VarCollectorVisitorTests {

	STSManager manager;
	VarDeclFactory df;
	ExprFactory ef;

	VarDecl<BoolType> a;
	VarDecl<IntType> b;
	VarDecl<RatType> c;
	VarDecl<BoolType> d;
	VarDecl<IntType> e;

	@Before
	public void before() {
		manager = new STSManagerImpl();
		ef = manager.getExprFactory();
		df = manager.getDeclFactory();

		a = df.Var("A", manager.getTypeFactory().Bool());
		b = df.Var("B", manager.getTypeFactory().Int());
		c = df.Var("C", manager.getTypeFactory().Rat());
		d = df.Var("D", manager.getTypeFactory().Bool());
		e = df.Var("E", manager.getTypeFactory().Int());
	}

	@SuppressWarnings("serial")
	@Test
	public void test() {
		Assert.assertTrue(checkExpr(ef.And(ImmutableSet.of(ef.True(), ef.False(), ef.Eq(ef.Int(1), ef.Int(2)))),
				new HashSet<VarDecl<? extends Type>>() {
					{
					}
				}));

		Assert.assertTrue(checkExpr(ef.And(ImmutableSet.of(a.getRef(), ef.Not(d.getRef()))),
				new HashSet<VarDecl<? extends Type>>() {
					{
						add(a);
						add(d);
					}
				}));

		Assert.assertTrue(
				checkExpr(
						ef.And(ImmutableSet.of(ef.Imply(a.getRef(), d.getRef()),
								ef.Eq(c.getRef(), ef.Sub(b.getRef(), e.getRef())))),
						new HashSet<VarDecl<? extends Type>>() {
							{
								add(a);
								add(b);
								add(c);
								add(d);
								add(e);
							}
						}));
	}

	private boolean checkExpr(final Expr<? extends Type> expr, final Set<VarDecl<? extends Type>> expectedVars) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		FormalismUtils.collectVars(expr, vars);
		return setContentEquals(vars, expectedVars);
	}

	private <T> boolean setContentEquals(final Set<T> set1, final Set<T> set2) {
		if (set1.size() != set2.size())
			return false;
		for (final T item : set1)
			if (!set2.contains(item))
				return false;
		return true;
	}
}
