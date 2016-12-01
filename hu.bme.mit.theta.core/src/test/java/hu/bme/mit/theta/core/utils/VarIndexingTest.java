package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.utils.impl.VarIndexing;

public class VarIndexingTest {

	final VarDecl<?> x = Var("x", Int());
	final VarDecl<?> y = Var("y", Int());
	final VarDecl<?> z = Var("z", Int());

	@Test
	public void testAll() {
		final VarIndexing all0 = VarIndexing.all(0);
		final VarIndexing all1 = VarIndexing.all(1);

		assertEquals(0, all0.get(x));
		assertEquals(0, all0.get(y));
		assertEquals(0, all0.get(z));

		assertEquals(1, all1.get(x));
		assertEquals(1, all1.get(y));
		assertEquals(1, all1.get(z));
	}

	@Test
	public void testInc() {
		final VarIndexing indexes = VarIndexing.builder(0).inc(x).inc(z).inc(x).build();

		assertEquals(2, indexes.get(x));
		assertEquals(0, indexes.get(y));
		assertEquals(1, indexes.get(z));
	}

	@Test
	public void testIncAll() {
		final VarIndexing indexing = VarIndexing.builder(0).inc(x).incAll().build();

		assertEquals(2, indexing.get(x));
		assertEquals(1, indexing.get(y));
		assertEquals(1, indexing.get(z));
	}

	@Test
	public void testJoin() {
		final VarIndexing indexes1 = VarIndexing.builder(0).inc(x).inc(y).build();
		final VarIndexing indexes2 = VarIndexing.builder(1).inc(x).inc(z).build();
		final VarIndexing joinedIndexes = indexes1.join(indexes2);
		
				assertEquals(2, joinedIndexes.get(x));
		assertEquals(1, joinedIndexes.get(y));
		assertEquals(2, joinedIndexes.get(z));
	}

}
