/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.collectVars
import hu.bme.mit.theta.xcfa.passes.getCMetaData
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

class TestExpressionParsing {

    @Test
    fun testInvariantParsing() {
        val stream = javaClass.getResourceAsStream("/24invariant.c")
        val parseContext = ParseContext()
        val xcfa = getXcfaFromC(
            stream!!,
            parseContext,
            false,
            false,
            validation = true,
            warningLogger = NullLogger.getInstance()
        )

        val proc = xcfa.first.initProcedures.first().first
        val ifBeforeReachErrorCall = proc.edges.filter { it.getCMetaData()?.let { it.lineNumberStart == 11 && it.colNumberStart == 8 } ?: false }.first()
        val invariant = "j + 2 < 10"

        val invariantExpr = parseCExpression(
            invariant,
            xcfa.first.collectVars().associateWith { CComplexType.getType(it.ref, parseContext) },
            ifBeforeReachErrorCall.getCMetaData()!!.scope.reversed(),
            NullLogger.getInstance()
        )

        val vars = ExprUtils.getVars(invariantExpr)
        Assertions.assertTrue(xcfa.first.collectVars().toSet().containsAll(vars))
    }
}