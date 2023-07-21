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
package hu.bme.mit.theta.common.pointerstore

import org.junit.Test
import org.junit.Assert

class PointerStoreTest {
    @Test
    fun testAddPointer() {
        val store = PointerStore()
        val s = PointerStoreMember("s", 0)
        val starS = PointerStoreMember("s", 1)
        val ampS = PointerStoreMember("s", -1)
        store.addPointer(s)

        Assert.assertEquals(store.pointsTo(s), setOf(starS))
        Assert.assertEquals(store.pointsTo(ampS), setOf(s))
    }
    @Test
    fun testPointsTo() {
        val store = PointerStore()
        val s = PointerStoreMember("s", 0)
        val starS = PointerStoreMember("s", 1)
        val ampS = PointerStoreMember("s", -1)
        store.addPointer(s)

        Assert.assertEquals(store.pointsTo(s), setOf(starS))
        Assert.assertEquals(store.pointsTo(ampS), setOf(s))

        val t = PointerStoreMember("t", 0)
        val starT = PointerStoreMember("t", 1)
        val ampT = PointerStoreMember("t", -1)

        store.addPointer(t)
        Assert.assertEquals(store.pointsTo(s), setOf(starS))
        Assert.assertEquals(store.pointsTo(ampS), setOf(s))
        Assert.assertEquals(store.pointsTo(t), setOf(starT))
        Assert.assertEquals(store.pointsTo(ampT), setOf(t))

        store.addPointsTo(s, t)

        Assert.assertEquals(store.pointsTo(s), setOf(starS, t))
    }
}
