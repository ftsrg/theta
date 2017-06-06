package hu.bme.mit.theta.core.model;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.util.HashMap;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class AssignmentTest {
	private final ConstDecl<IntType> ca = Const("a", Int());
	private final ConstDecl<IntType> cb = Const("b", Int());

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
