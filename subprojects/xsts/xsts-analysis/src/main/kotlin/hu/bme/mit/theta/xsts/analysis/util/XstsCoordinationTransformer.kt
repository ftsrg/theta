/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xsts.analysis.util

import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.enumtype.EnumEqExpr
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr
import hu.bme.mit.theta.xsts.XSTS

fun transform(xsts: XSTS): XSTS {

    /*
    Transforms XSTS of the form

    env {

    if (coordState == q0) {
        <env of Sensor1>
        scheduled := Sensor1
    }
    if (coordState == q1) { ... }
    if (coordState == q2) { ... }
    if (coordState == q3) { ... }
    }

    tran {
    __delay;
    if (scheduled == Sensor1) { <tran of Sensor1> }
    if (scheduled == Sensor2) { <tran of Sensor2> }
    ... // Sensor3, Sensor4, PrimaryRWA, SecondaryRWA
    }

    to

    env {}

    tran {
        __delay;
        <env of Sensor1>
        <tran of Sensor1>
    } or {
        __delay;
        <env of Sensor2>
        <tran of Sensor2>
    }

     */

    val delays = mutableListOf<Stmt>()

    assert(xsts.tran.stmts.size == 1)
    val tranSeq = xsts.tran.stmts[0] as SequenceStmt
    for (i in 0 until tranSeq.stmts.size) {
        if (tranSeq.stmts[i] is IfStmt) break
        else delays.add(tranSeq.stmts[i])
    }
    val delayStmt = SequenceStmt.of(delays)
    val schedulings = mutableMapOf<EnumLitExpr,Stmt>()
    tranSeq.stmts.filterIsInstance<IfStmt>().forEach {
        schedulings[(it.cond as EnumEqExpr).rightOp as EnumLitExpr] = SequenceStmt.of(listOf(delayStmt, it.then))
    }

    assert(xsts.env.stmts.size == 1)
    val envChoice = xsts.env.stmts[0] as NonDetStmt
    val branches = envChoice.stmts.filterIsInstance<SequenceStmt>().map {
        SequenceStmt.of(it.stmts.map {
            if (it is AssignStmt<*> && it.expr is EnumLitExpr && schedulings.keys.contains(it.expr)) {
                schedulings[it.expr]!!
            } else {
                it
            }
        })
    }.toList()

    val newTran = NonDetStmt.of(branches)
    val newEnv = NonDetStmt.of(listOf())
    return XSTS(xsts.stateVars, xsts.localVars, xsts.ctrlVars, xsts.init, newTran, newEnv, xsts.initFormula, xsts.prop)
}