package hu.bme.mit.inf.theta.formalism.utils;

import static hu.bme.mit.inf.theta.core.type.impl.Types.Int;
import static hu.bme.mit.inf.theta.formalism.common.decl.impl.Decls2.Var;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.utils.VarIndexes;

public class VarIndexesTest {

	final VarDecl<?> x = Var("x", Int());
	final VarDecl<?> y = Var("y", Int());
	final VarDecl<?> z = Var("z", Int());

	@Test
	public void testAll() {
		final VarIndexes all0 = VarIndexes.all(0);
		final VarIndexes all1 = VarIndexes.all(1);

		assertEquals(0, all0.get(x));
		assertEquals(0, all0.get(y));
		assertEquals(0, all0.get(z));

		assertEquals(1, all1.get(x));
		assertEquals(1, all1.get(y));
		assertEquals(1, all1.get(z));
	}

	@Test
	public void testInc() {
		final VarIndexes indexes = VarIndexes.builder(0).inc(x).inc(z).inc(x).build();

		assertEquals(2, indexes.get(x));
		assertEquals(0, indexes.get(y));
		assertEquals(1, indexes.get(z));
	}

	@Test
	public void testIncAll() {
		final VarIndexes indexes = VarIndexes.builder(0).inc(x).incAll().build();

		assertEquals(2, indexes.get(x));
		assertEquals(1, indexes.get(y));
		assertEquals(1, indexes.get(z));
	}

}
