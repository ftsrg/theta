package hu.bme.mit.theta.core.model;

import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;
import static hu.bme.mit.theta.core.type.impl.Types.Int;

import java.util.HashMap;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.impl.Decls;
import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.theta.core.type.IntType;

public class AssignmentTest {
	private final ConstDecl<IntType> ca = Decls.Const("a", Int());
	private final ConstDecl<IntType> cb = Decls.Const("b", Int());

	@Test
	public void testNullary() {
		final Assignment assignment = AssignmentImpl.empty();

		Assert.assertEquals(assignment.toExpr(), True());
	}

	@Test
	public void testUnary() {
		final Map<Decl<?>, LitExpr<?>> declToExpr = new HashMap<>();
		declToExpr.put(ca, Int(5));
		final Assignment assignment = new AssignmentImpl(declToExpr);

		Assert.assertEquals(assignment.toExpr(), Eq(ca.getRef(), Int(5)));
	}

	@Test
	public void testMultiary() {
		final Map<Decl<?>, LitExpr<?>> declToExpr = new HashMap<>();
		declToExpr.put(ca, Int(5));
		declToExpr.put(cb, Int(9));
		final Assignment assignment = new AssignmentImpl(declToExpr);

		Assert.assertEquals(assignment.toExpr(), And(Eq(ca.getRef(), Int(5)), Eq(cb.getRef(), Int(9))));
	}
}
