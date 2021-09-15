/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import org.junit.Test;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.assertEquals;

public class VarIndexingTest {

	final VarDecl<?> x = Var("x", Int());
	final VarDecl<?> y = Var("y", Int());
	final VarDecl<?> z = Var("z", Int());

	@Test
	public void testAll() {
		final VarIndexing all0 = VarIndexingFactory.indexing(0);
		final VarIndexing all1 = VarIndexingFactory.indexing(1);

		assertEquals(0, all0.get(x));
		assertEquals(0, all0.get(y));
		assertEquals(0, all0.get(z));

		assertEquals(1, all1.get(x));
		assertEquals(1, all1.get(y));
		assertEquals(1, all1.get(z));
	}

	@Test
	public void testInc() {
		final VarIndexing indexes = VarIndexingFactory.indexingBuilder(0).inc(x).inc(z).inc(x).build();

		assertEquals(2, indexes.get(x));
		assertEquals(0, indexes.get(y));
		assertEquals(1, indexes.get(z));
	}

	@Test
	public void testIncNeg() {
		final VarIndexing indexes = VarIndexingFactory.basicIndexingBuilder(2).inc(x, -1).inc(z, -1).inc(x, -1).build();

		assertEquals(0, indexes.get(x));
		assertEquals(2, indexes.get(y));
		assertEquals(1, indexes.get(z));
	}

	@Test(expected = IllegalArgumentException.class)
	public void testIncNegException() {
		VarIndexingFactory.basicIndexingBuilder(1).inc(x, -1).inc(z, -1).inc(x, -1).build();
	}

	@Test
	public void testIncAll() {
		final VarIndexing indexing = VarIndexingFactory.indexingBuilder(0).inc(x).incAll().build();

		assertEquals(2, indexing.get(x));
		assertEquals(1, indexing.get(y));
		assertEquals(1, indexing.get(z));
	}

	@Test
	public void testJoin() {
		final VarIndexing indexes1 = VarIndexingFactory.indexingBuilder(0).inc(x).inc(y).build();
		final VarIndexing indexes2 = VarIndexingFactory.indexingBuilder(1).inc(x).inc(z).build();
		final VarIndexing joinedIndexes = indexes1.join(indexes2);

		assertEquals(2, joinedIndexes.get(x));
		assertEquals(1, joinedIndexes.get(y));
		assertEquals(2, joinedIndexes.get(z));
	}

	@Test
	public void testSub() {
		final VarIndexing indexes1 = VarIndexingFactory.indexingBuilder(1).inc(x).inc(y).inc(y).build();
		final VarIndexing indexes2 = VarIndexingFactory.indexingBuilder(0).inc(x).inc(z).build();
		final VarIndexing sub = indexes1.sub(indexes2);
		assertEquals(1, sub.get(x));
		assertEquals(3, sub.get(y));
		assertEquals(0, sub.get(z));
	}

	@Test
	public void testSub2() {
		final VarIndexing indexes1 = VarIndexingFactory.indexingBuilder(5).build();
		final VarIndexing indexes2 = VarIndexingFactory.indexingBuilder(2).build();
		final VarIndexing sub = indexes1.sub(indexes2);
		assertEquals(3, sub.get(x));
		assertEquals(3, sub.get(y));
		assertEquals(3, sub.get(z));
	}

	@Test(expected = IllegalArgumentException.class)
	public void testSubException() {
		final VarIndexing indexes1 = VarIndexingFactory.indexingBuilder(1).inc(x).build();
		final VarIndexing indexes2 = VarIndexingFactory.indexingBuilder(0).inc(x).inc(x).inc(x).build();
		indexes1.sub(indexes2);
	}

	@Test(expected = IllegalArgumentException.class)
	public void testSubException2() {
		final VarIndexing indexes1 = VarIndexingFactory.indexingBuilder(1).build();
		final VarIndexing indexes2 = VarIndexingFactory.indexingBuilder(2).build();
		indexes1.sub(indexes2);
	}

}
