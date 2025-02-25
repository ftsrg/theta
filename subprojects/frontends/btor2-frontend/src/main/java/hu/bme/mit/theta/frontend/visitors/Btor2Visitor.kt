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

package hu.bme.mit.theta.frontend.visitors

import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import hu.bme.mit.theta.frontend.models.*

class Btor2Visitor : Btor2BaseVisitor<Btor2Circuit>(){
    private val sortVisitor = SortVisitor()
    private val constantVisitor = ConstantVisitor()
    private val operationVisitor = OperationVisitor()
    private val statefulVisitor = StateVisitor()

    override fun visitLine(ctx: Btor2Parser.LineContext?): Btor2Circuit {
        for (child in ctx?.children!!) {
            println(child.accept(this))
        }
        return Btor2Circuit
    }

    override fun visitSort(ctx: Btor2Parser.SortContext?): Btor2Circuit {
        val result = sortVisitor.visit(ctx)
        println(result)
        Btor2Circuit.sorts[result.sid] = result
        return Btor2Circuit
    }

    override fun visitConstantNode(ctx: Btor2Parser.ConstantNodeContext): Btor2Circuit {
        println(constantVisitor.visit(ctx))
        return Btor2Circuit
    }

    override fun visitOperation(ctx: Btor2Parser.OperationContext): Btor2Circuit {
        println(operationVisitor.visit(ctx))
        return Btor2Circuit
    }

    override fun visitStateful(ctx: Btor2Parser.StatefulContext?): Btor2Circuit {
        println(statefulVisitor.visit(ctx))
        return Btor2Circuit
    }


}