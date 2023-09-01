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
package hu.bme.mit.theta.frontend

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.DivExpr
import hu.bme.mit.theta.core.type.abstracttype.MulExpr
import hu.bme.mit.theta.frontend.transformation.model.statements.*

data class CStatistics(
    val globalDeclarations: Int,
    val functions: Collection<CFunctionStatistics>,
)

data class CFunctionStatistics(
    val variables: Int,
    val loopNumber: Int,
    val deepestLoop: Int,
    val linear: Boolean,
)

fun CProgram.getStatistics(): CStatistics {
    return CStatistics(
        globalDeclarations = globalDeclarations.size,
        functions = functions.map {
            val (loopNumber, deepestLoop, linear) = it.collectStatistics()
            CFunctionStatistics(
                variables = it.flatVariables.size,
                loopNumber = loopNumber,
                deepestLoop = deepestLoop,
                linear = linear
            )
        }
    )
}

fun CFunction.collectStatistics(): Triple<Int, Int, Boolean> {
    val statisticsCollectorVisitor = StatisticsCollectorVisitor()
    this.compound?.accept(statisticsCollectorVisitor, Unit)
    return Triple(statisticsCollectorVisitor.loopNumber, statisticsCollectorVisitor.deepestLoop,
        statisticsCollectorVisitor.linear)
}

fun Expr<*>.isNonLinear(): Boolean {
    if (this is MulExpr<*> || this is DivExpr<*>) {
        return true;
    } else if (this.ops.size > 0) {
        return this.ops.any { it.isNonLinear() }
    } else return false;
}

class StatisticsCollectorVisitor : CStatementVisitor<Unit, Unit> {

    var loopNumber = 0
        private set
    var deepestLoop = 0
        private set
    var linear = true
        private set

    private var currentDepth = 0

    override fun visit(statement: CAssignment, param: Unit) {
        val lval = statement.getlValue()
        if (linear && lval.isNonLinear()) linear = false
        statement.getrValue()?.accept(this, param)
    }

    override fun visit(statement: CAssume, param: Unit) {
        if (linear && statement.assumeStmt.cond.isNonLinear()) linear = false
    }

    override fun visit(statement: CBreak, param: Unit) {
    }

    override fun visit(statement: CCall, param: Unit) {
        statement.params.forEach { it?.accept(this, param) }
    }

    override fun visit(statement: CCase, param: Unit) {
        statement.expr?.accept(this, param)
        statement.statement?.accept(this, param)
    }

    override fun visit(statement: CCompound, param: Unit) {
        statement.getcStatementList().forEach { it?.accept(this, param) }
    }

    override fun visit(statement: CContinue, param: Unit) {
    }

    override fun visit(statement: CDecls, param: Unit) {
        statement.getcDeclarations().map { it.get1().initExpr?.accept(this, param) }
    }

    override fun visit(statement: CDefault, param: Unit) {
        statement.statement?.accept(this, param)
    }

    override fun visit(statement: CDoWhile, param: Unit) {
        loopNumber++
        statement.guard?.accept(this, param)
        currentDepth++
        if (deepestLoop < currentDepth) deepestLoop = currentDepth
        statement.body?.accept(this, param)
        currentDepth--
    }

    override fun visit(statement: CExpr, param: Unit) {
        if (linear && statement.expr?.isNonLinear() == true) linear = false
    }

    override fun visit(statement: CFor, param: Unit) {
        loopNumber++
        statement.init?.accept(this, param)
        statement.guard?.accept(this, param)
        statement.increment?.accept(this, param)
        currentDepth++
        if (deepestLoop < currentDepth) deepestLoop = currentDepth
        statement.body?.accept(this, param)
        currentDepth--
    }

    override fun visit(statement: CFunction, param: Unit) {
        System.err.println("WARNING: Should not be here (CFUnction embedding not supported)")
    }

    override fun visit(statement: CGoto, param: Unit) {
    }

    override fun visit(statement: CIf, param: Unit) {
        statement.guard?.accept(this, param)
        statement.body?.accept(this, param)
    }

    override fun visit(statement: CInitializerList, param: Unit) {
        statement.statements.forEach { it.get1().map { it?.accept(this, param) }; it.get2()?.accept(this, param) }
    }

    override fun visit(statement: CProgram, param: Unit) {
        System.err.println("WARNING: Should not be here (CProgram embedding not supported)")
    }

    override fun visit(statement: CRet, param: Unit) {
        statement.expr?.accept(this, param);
    }

    override fun visit(statement: CSwitch, param: Unit) {
        statement.testValue?.accept(this, param)
        statement.body?.accept(this, param)
    }

    override fun visit(statement: CWhile, param: Unit) {
        loopNumber++
        statement.guard?.accept(this, param)
        currentDepth++
        if (deepestLoop < currentDepth) deepestLoop = currentDepth
        statement.body?.accept(this, param)
        currentDepth--
    }
}

