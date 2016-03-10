package hu.bme.mit.inf.ttmc.formalism.tests;

import java.util.HashSet;
import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.VarCollectorVisitor;
import org.junit.Assert;

public class VarCollectorVisitorTests {
	
	STSManager manager;
	VarDeclFactory df;
	ExprFactory ef;

	VarDecl<BoolType> a;
	VarDecl<IntType> b;
	VarDecl<RatType> c;
	VarDecl<BoolType> d;
	VarDecl<IntType> e;
	
	VarCollectorVisitor visitor;
	
	@Before
	public void before() {
		manager = new STSManagerImpl(new ConstraintManagerImpl());
		ef = manager.getExprFactory();
		df = manager.getDeclFactory();

		a = df.Var("A", manager.getTypeFactory().Bool());
		b = df.Var("B", manager.getTypeFactory().Int());
		c = df.Var("C", manager.getTypeFactory().Rat());
		d = df.Var("D", manager.getTypeFactory().Bool());
		e = df.Var("E", manager.getTypeFactory().Int());
		
		visitor = new VarCollectorVisitor();
	}

	@SuppressWarnings("serial")
	@Test
	public void test() {
		Assert.assertTrue(checkExpr(
				ef.And(ImmutableSet.of(ef.True(), ef.False(), ef.Eq(ef.Int(1), ef.Int(2)))),
				new HashSet<VarDecl<? extends Type>>() {{}}));

		Assert.assertTrue(checkExpr(
				ef.And(ImmutableSet.of(a.getRef(), ef.Not(d.getRef()))),
				new HashSet<VarDecl<? extends Type>>() {{add(a); add(d);}}));
		
		Assert.assertTrue(checkExpr(
				ef.And(ImmutableSet.of(ef.Imply(a.getRef(), d.getRef()), ef.Eq(c.getRef(), ef.Sub(b.getRef(), e.getRef())))),
				new HashSet<VarDecl<? extends Type>>() {{add(a); add(b); add(c); add(d); add(e);}}));
	}
	
	private boolean checkExpr(Expr<? extends Type> expr, Set<VarDecl<? extends Type>> expectedVars) {
		Set<VarDecl<? extends Type>> vars = new HashSet<>();
		expr.accept(visitor, vars);
		return setContentEquals(vars, expectedVars);
	}
	
	private <T> boolean setContentEquals(Set<T> set1, Set<T> set2) {
		if (set1.size() != set2.size()) return false;
		for (T item : set1) if (!set2.contains(item)) return false;
		return true;
	}
}
