/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.utils

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.inttype.IntExprs
import org.junit.Assert
import org.junit.Test

class PointerStoreTest {

    @Test
    fun testIsLeq() {
        val pointerStore1 = PointerStore()
        val pointerStore2 = PointerStore()
        val p = Decls.Var("p", IntExprs.Int())
        val q = Decls.Var("q", IntExprs.Int())
        val a = Decls.Var("a", IntExprs.Int())
        val b = Decls.Var("b", IntExprs.Int())

        pointerStore1.addPointsTo(p, a)
        pointerStore2.addPointsTo(p, a)
        // s1: p -> a
        // s2: p -> a
        // s1 <= s2, s2 <= s1
        Assert.assertTrue(pointerStore1.isLeq(pointerStore2))
        Assert.assertTrue(pointerStore2.isLeq(pointerStore1))

        // s1: p -> a
        // s2: p -> a, q -> b
        // s1 <= s2, s2 !<= s1
        pointerStore2.addPointsTo(q, b)
        Assert.assertTrue(pointerStore1.isLeq(pointerStore2))
        Assert.assertFalse(pointerStore2.isLeq(pointerStore1))

        // s1: p -> a, q -> b
        // s2: p -> a, q -> a
        // s1 !<= s2, s2 !<= s1
        pointerStore1.addPointsTo(q, a)
        Assert.assertFalse(pointerStore1.isLeq(pointerStore2))
        Assert.assertFalse(pointerStore2.isLeq(pointerStore1))
    }
}