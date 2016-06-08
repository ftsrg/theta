package hu.bme.mit.inf.ttmc.formalism.utils.tests;

import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.utils.VarIndexes;

public class VarIndexesTests {

	final VarDecl<?> x = Var("x", Int());
	final VarDecl<?> y = Var("y", Int());
	final VarDecl<?> z = Var("z", Int());

	@Test
	public void testAll() {
		final VarIndexes all0 = VarIndexes.all(0);
		final VarIndexes all1 = VarIndexes.all(1);

		assertEquals(0, all0.getIndex(x));
		assertEquals(0, all0.getIndex(y));
		assertEquals(0, all0.getIndex(z));

		assertEquals(1, all1.getIndex(x));
		assertEquals(1, all1.getIndex(y));
		assertEquals(1, all1.getIndex(z));
	}

	@Test
	public void testInc() {
		final VarIndexes indexes = VarIndexes.builder(0).inc(x).inc(z).inc(x).build();

		assertEquals(2, indexes.getIndex(x));
		assertEquals(0, indexes.getIndex(y));
		assertEquals(1, indexes.getIndex(z));
	}

	@Test
	public void testIncAll() {
		final VarIndexes indexes = VarIndexes.builder(0).inc(x).incAll().build();

		assertEquals(2, indexes.getIndex(x));
		assertEquals(1, indexes.getIndex(y));
		assertEquals(1, indexes.getIndex(z));
	}

}
