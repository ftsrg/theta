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
package hu.bme.mit.theta.common.disjointset

import org.junit.Test
import org.junit.Assert

class DisjointSetTest {
    @Test
    fun testMakeSet() {
        val set = DisjointSet<Int>()
        set.makeSet(1)
        set.makeSet(2)
        set.makeSet(3)

        Assert.assertEquals(set.find(1), 1)
        Assert.assertEquals(set.find(2), 2)
        Assert.assertEquals(set.find(3), 3)
    }

    @Test
    fun testUnion() {
        val set = DisjointSet<Int>()
        set.makeSet(1)
        set.makeSet(2)

        set.union(1, 2)
        Assert.assertEquals(set.find(1), set.find(2))

        set.makeSet(3)
        set.union(1, 3)
        Assert.assertEquals(set.find(1), set.find(2))
        Assert.assertEquals(set.find(1), set.find(3))
        Assert.assertEquals(set.find(2), set.find(3))
    }

    @Test
    fun testUnionComplex() {
        val set = DisjointSet<Int>()
        set.makeSet(1)
        set.makeSet(2)
        set.makeSet(3)
        set.makeSet(4)
        set.makeSet(5)
        set.makeSet(6)
        set.makeSet(7)
        set.makeSet(8)
        set.makeSet(9)
        set.makeSet(10)

        set.union(1, 2)
        set.union(3, 4)
        set.union(5, 6)
        set.union(7, 8)
        set.union(9, 10)
        set.union(2, 4)
        set.union(6, 8)
        set.union(1, 3)
        set.union(5, 7)
        set.union(2, 6)
        set.union(1, 5)
        set.union(2, 3)
        set.union(5, 9)

        Assert.assertEquals(set.find(1), set.find(2))
        Assert.assertEquals(set.find(1), set.find(3))
        Assert.assertEquals(set.find(1), set.find(4))
        Assert.assertEquals(set.find(1), set.find(5))
        Assert.assertEquals(set.find(1), set.find(6))
        Assert.assertEquals(set.find(1), set.find(7))
        Assert.assertEquals(set.find(1), set.find(8))
        Assert.assertEquals(set.find(1), set.find(9))
        Assert.assertEquals(set.find(1), set.find(10))
    }

    @Test (expected = IllegalArgumentException::class)
    fun testFindException() {
        val set = DisjointSet<Int>()
        set.find(1)
    }

    @Test (expected = IllegalArgumentException::class)
    fun testUnionException() {
        val set = DisjointSet<Int>()
        set.makeSet(1)
        set.union(1, 2)
    }
}
