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

package hu.bme.mit.theta.analysis.algorithm.mcm

import hu.bme.mit.theta.core.decl.VarDecl


open class MemoryEvent(protected val type: MemoryEventType, protected val tag: String, protected val id: Int) {

    fun tag(): String {
        return tag
    }

    enum class MemoryEventType(val label: String) {
        READ("R"),
        WRITE("W"),
        FENCE("F"),
        META("M")
    }

    fun type(): MemoryEventType {
        return type
    }

    open fun asRead(): Read {
        throw UnsupportedOperationException("Not a read!")
    }

    open fun asWrite(): Write {
        throw UnsupportedOperationException("Not a write!")
    }

    open fun asFence(): Fence {
        throw UnsupportedOperationException("Not a fence!")
    }

    open fun asMemoryIO(): MemoryIO {
        throw UnsupportedOperationException("Not memory IO!")
    }

    abstract class MemoryIO(id: Int, private val `var`: VarDecl<*>, private val localVar: VarDecl<*>,
        type: MemoryEventType, tag: String) :
        MemoryEvent(type, tag, id) {

        override fun asMemoryIO(): MemoryIO {
            return this
        }

        override fun toString(): String {
            return type.toString() + "{" +
                "var=" + `var` +
                ", localVar=" + localVar +
                ", tag=" + tag +
                ", id=" + id +
                '}'
        }

        fun `var`(): VarDecl<*> {
            return `var`
        }

        fun localVar(): VarDecl<*> {
            return localVar
        }
    }

    class Read(id: Int, `var`: VarDecl<*>, localVar: VarDecl<*>, tag: String) :
        MemoryIO(id, `var`, localVar, MemoryEventType.READ, tag) {

        override fun asRead(): Read {
            return this
        }
    }

    class Write(id: Int, `var`: VarDecl<*>, localVar: VarDecl<*>, private val dependencies: Set<VarDecl<*>>,
        tag: String) :
        MemoryIO(id, `var`, localVar, MemoryEventType.WRITE, tag) {

        override fun asWrite(): Write {
            return this
        }

        fun dependencies(): Set<VarDecl<*>> {
            return dependencies
        }
    }

    class Fence(id: Int, tag: String) : MemoryEvent(MemoryEventType.FENCE, tag, id) {

        override fun asFence(): Fence {
            return this
        }

        override fun toString(): String {
            return type.toString() + "{" +
                "tag='" + tag + '\'' +
                '}'
        }
    }
}