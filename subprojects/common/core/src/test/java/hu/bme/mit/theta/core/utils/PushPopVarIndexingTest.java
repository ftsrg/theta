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
import hu.bme.mit.theta.core.utils.indexings.PushPopVarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import org.junit.Test;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.assertEquals;

public class PushPopVarIndexingTest {

	final VarDecl<?> x = Var("x", Int());
	final VarDecl<?> y = Var("y", Int());
	final VarDecl<?> z = Var("z", Int());

	@Test
	public void testPushPop() {
		final VarIndexing indexing0 = VarIndexingFactory.pushPopIndexingBuilder(0).build();
		final VarIndexing indexing1 = VarIndexingFactory.pushPopIndexingBuilder(0).push(x).build();
		final VarIndexing indexing2 = VarIndexingFactory.pushPopIndexingBuilder(0).push(x).inc(x).build();
		final VarIndexing indexing3 = VarIndexingFactory.pushPopIndexingBuilder(0).push(x).inc(x).inc(x).build();
		final VarIndexing indexing4 = VarIndexingFactory.pushPopIndexingBuilder(0).push(x).inc(x).inc(x).pop(x).build();
		final VarIndexing indexing5 = VarIndexingFactory.pushPopIndexingBuilder(0).push(x).inc(x).inc(x).pop(x).inc(x).build();
		assertEquals(0, indexing0.get(x));
		assertEquals(1, indexing1.get(x));
		assertEquals(2, indexing2.get(x));
		assertEquals(3, indexing3.get(x));
		assertEquals(0, indexing4.get(x));
		assertEquals(4, indexing5.get(x));
	}

	@Test
	public void testPopPush() {
		final VarIndexing indexing0 = VarIndexingFactory.pushPopIndexingBuilder(0).build();
		final VarIndexing indexing1 = VarIndexingFactory.pushPopIndexingBuilder(0).pop(x).build();
		final VarIndexing indexing2 = VarIndexingFactory.pushPopIndexingBuilder(0).pop(x).inc(x).build();
		final VarIndexing indexing3 = VarIndexingFactory.pushPopIndexingBuilder(0).pop(x).inc(x).inc(x).build();
		final VarIndexing indexing4 = VarIndexingFactory.pushPopIndexingBuilder(0).pop(x).inc(x).inc(x).push(x).build();
		final VarIndexing indexing5 = VarIndexingFactory.pushPopIndexingBuilder(0).pop(x).inc(x).inc(x).push(x).inc(x).build();
		assertEquals(0, indexing0.get(x));
		assertEquals(0, indexing1.get(x));
		assertEquals(1, indexing2.get(x));
		assertEquals(2, indexing3.get(x));
		assertEquals(3, indexing4.get(x));
		assertEquals(4, indexing5.get(x));
	}

	@Test
	public void testAdd() {
		final VarIndexing indexing0 = VarIndexingFactory.pushPopIndexingBuilder(0).build();
		final VarIndexing indexing1 = VarIndexingFactory.pushPopIndexingBuilder(0).push(x).build();
		final VarIndexing indexing2 = indexing0.add(indexing1);
		assertEquals(0, indexing0.get(x));
		assertEquals(1, indexing1.get(x));
		assertEquals(1, indexing2.get(x));
	}

	@Test
	public void testPopAdd() {
		final VarIndexing indexing0 = VarIndexingFactory.pushPopIndexingBuilder(0).push(x).build();
		final VarIndexing indexing1 = VarIndexingFactory.pushPopIndexingBuilder(0).pop(x).inc(x).build();
		final PushPopVarIndexing indexing2 = (PushPopVarIndexing) indexing0.add(indexing1);
		final VarIndexing indexing3 = indexing2.pop(x);
		assertEquals(1, indexing0.get(x));
		assertEquals(1, indexing1.get(x));
		assertEquals(2, indexing2.get(x));
		assertEquals(0, indexing3.get(x));
	}

	@Test
	public void testPopSub() {
		final VarIndexing indexing0 = VarIndexingFactory.pushPopIndexingBuilder(Integer.MAX_VALUE).build();
		final VarIndexing indexing1 = VarIndexingFactory.pushPopIndexingBuilder(0).pop(x).inc(x).build();
		final PushPopVarIndexing indexing2 = (PushPopVarIndexing) indexing0.sub(indexing1);
		assertEquals(Integer.MAX_VALUE, indexing0.get(x));
		assertEquals(1, indexing1.get(x));
		assertEquals(Integer.MAX_VALUE, indexing2.get(x));
	}


}
