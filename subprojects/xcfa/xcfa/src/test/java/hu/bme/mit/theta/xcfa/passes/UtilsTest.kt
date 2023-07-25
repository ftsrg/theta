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

package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts.*
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class UtilsTest {

    companion object {

        private val x = Var("x", Int())
        private val y = Var("y", Int())
        private val xPrime = Var("x'", Int())
        private val map: Map<Decl<*>, VarDecl<*>> = mapOf(Pair(x, xPrime))

        @JvmStatic
        fun getLabels(): List<Arguments> = listOf(
            Arguments.of(InvokeLabel("", listOf(x.ref, y.ref), EmptyMetaData),
                InvokeLabel("", listOf(xPrime.ref, y.ref), EmptyMetaData)),
            Arguments.of(JoinLabel(x, EmptyMetaData), JoinLabel(xPrime, EmptyMetaData)),
            Arguments.of(NondetLabel(setOf(NopLabel), EmptyMetaData), NondetLabel(setOf(NopLabel), EmptyMetaData)),
            Arguments.of(SequenceLabel(listOf(NopLabel), EmptyMetaData),
                SequenceLabel(listOf(NopLabel), EmptyMetaData)),
            Arguments.of(ReadLabel(x, y, setOf(), EmptyMetaData), ReadLabel(xPrime, y, setOf(), EmptyMetaData)),
            Arguments.of(WriteLabel(x, y, setOf(), EmptyMetaData), WriteLabel(xPrime, y, setOf(), EmptyMetaData)),
            Arguments.of(FenceLabel(setOf(), EmptyMetaData), FenceLabel(setOf(), EmptyMetaData)),
            Arguments.of(StartLabel("", listOf(x.ref), y, EmptyMetaData),
                StartLabel("", listOf(xPrime.ref), y, EmptyMetaData)),
            Arguments.of(ReturnLabel(JoinLabel(x, EmptyMetaData)), ReturnLabel(JoinLabel(xPrime, EmptyMetaData))),

            Arguments.of(StmtLabel(Assign(x, y.ref), metadata = EmptyMetaData),
                StmtLabel(Assign(xPrime, y.ref), metadata = EmptyMetaData)),
            Arguments.of(StmtLabel(Havoc(x), metadata = EmptyMetaData),
                StmtLabel(Havoc(xPrime), metadata = EmptyMetaData)),
            Arguments.of(StmtLabel(Assume(Eq(x.ref, y.ref)), metadata = EmptyMetaData),
                StmtLabel(Assume(Eq(xPrime.ref, y.ref)), metadata = EmptyMetaData)),
            Arguments.of(StmtLabel(Skip(), metadata = EmptyMetaData), StmtLabel(Skip(), metadata = EmptyMetaData)),
        )
    }

    @ParameterizedTest
    @MethodSource("getLabels")
    fun testChangeVars(labelIn: XcfaLabel, labelExp: XcfaLabel) {
        Assertions.assertEquals(labelExp, labelIn.changeVars(map))
    }

}