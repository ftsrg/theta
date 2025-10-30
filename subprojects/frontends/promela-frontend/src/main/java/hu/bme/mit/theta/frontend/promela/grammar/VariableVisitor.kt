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
package hu.bme.mit.theta.frontend.promela.grammar

import hu.bme.mit.theta.frontend.promela.model.PromelaExpression
import hu.bme.mit.theta.frontend.promela.model.Variable
import hu.bme.mit.theta.frontend.promela.model.VariableInitialization
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaBaseVisitor
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaParser

class VariableInitVisitor(val exprVisitor : ExprVisitor) : promelaBaseVisitor<VariableInitialization>() {
    override fun visitIvar(ctx: promelaParser.IvarContext?): VariableInitialization {
        val name = ctx!!.Name().text
        if (ctx.Const() != null) {
            // TODO array init
            throw NotImplementedError()
        }
        if (ctx.ch_init() != null) {
            // TODO ch init
            throw NotImplementedError()
        } else {
            val promelaExpression : PromelaExpression = ctx.any_expr().accept(exprVisitor)
            return VariableInitialization(Variable(name), promelaExpression)
        }
    }
}