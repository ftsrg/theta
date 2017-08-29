package hu.bme.mit.theta.analysis.expl;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.util.Optional;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.BasicValuation;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class ExplStateTest {

	private final VarDecl<IntType> x = Var("x", Int());
	private final VarDecl<IntType> y = Var("y", Int());

	@Test
	public void testInstances() {
		final ExplState t1 = ExplState.createTop();
		final ExplState t2 = ExplState.createTop();
		final ExplState t3 = ExplState.create(BasicValuation.empty());
		final ExplState s1 = ExplState.create(BasicValuation.builder().put(x, Int(1)).build());
		final ExplState s2 = ExplState.create(BasicValuation.builder().put(x, Int(1)).build());

		Assert.assertTrue(t1 == t2);
		Assert.assertTrue(t1 == t3);
		Assert.assertTrue(t2 == t3);

		Assert.assertTrue(s1 != t1);
		Assert.assertEquals(s1, s2);
	}

	@Test
	public void testEval() {
		final ExplState s1 = ExplState.create(BasicValuation.builder().put(x, Int(1)).build());

		Assert.assertEquals(Optional.of(Int(1)), s1.eval(x));
		Assert.assertEquals(Optional.empty(), s1.eval(y));
	}
}
