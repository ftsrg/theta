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

import hu.bme.mit.theta.frontend.promela.model.*
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaBaseVisitor
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaParser

class SequenceVisitor : promelaBaseVisitor<Sequence>() {
    val stepVisitor = StepVisitor()

    override fun visitSequence(ctx: promelaParser.SequenceContext?): Sequence {
        val steps = ctx!!.step().map { it.accept(stepVisitor) }.toList()
    }
}

class StepVisitor(val decl_lstVisitor : Decl_lstVisitor) : promelaBaseVisitor<Step>() {
    val statementVisitor = StatementVisitor()

    override fun visitStmnts(ctx: promelaParser.StmntsContext?): Step {
         return StmntsStep(ctx!!.stmnt().map { it.accept(statementVisitor) }.toList())
    }

    override fun visitDeclLst(ctx: promelaParser.DeclLstContext?): Step {
        return DeclListStep(ctx!!.decl_lst().accept(decl_lstVisitor))
    }

    override fun visitXr(ctx: promelaParser.XrContext?): Step {
        throw NotImplementedError()
    }

    override fun visitXs(ctx: promelaParser.XsContext?): Step {
        throw NotImplementedError()
    }
}