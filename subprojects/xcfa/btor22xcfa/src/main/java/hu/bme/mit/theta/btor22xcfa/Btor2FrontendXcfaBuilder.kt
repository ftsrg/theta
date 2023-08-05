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
package hu.bme.mit.theta.btor22xcfa

import Btor2BvSort
import Btor2Const
import Btor2Sort
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.arraytype.*
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.frontend.model.*
import hu.bme.mit.theta.frontend.model.Btor2NodeVisitor
import hu.bme.mit.theta.frontend.transformation.model.statements.*
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import kotlin.collections.LinkedHashSet

class Btor2FrontendXcfaBuilder(val sorts : HashMap<UInt, Btor2Sort>, val nodes : HashMap<UInt, Btor2Node>) :
    Btor2NodeVisitor<ParamPack, ParamPack> {
    private val visitedNodes = LinkedHashSet<Btor2Node>()
    private val builder = XcfaBuilder("TODO")

    fun buildXcfa(): XcfaBuilder {
        for (node in nodes.values) {
            if (!visitedNodes.contains(node)) {
                node.accept(this)
                visitedNodes.add(node)
            } else {

            }
        }
    }

    override fun visit(node: Btor2UnaryOperation, param: ParamPack): ParamPack {
        node.operand.accept(this, param)

        when (node.operator) {
            Btor2UnaryOperator.NOT -> AbstractExprs.Neg<>() // bitwise negation
            Btor2UnaryOperator.INC -> AbstractExprs.Add()
            Btor2UnaryOperator.DEC -> AbstractExprs.Sub()
            Btor2UnaryOperator.NEG -> TODO() // arithmetic negation
            Btor2UnaryOperator.REDAND -> TODO()
            Btor2UnaryOperator.REDOR -> TODO()
            Btor2UnaryOperator.REDXOR -> TODO()
        }
    }

    override fun visit(node: Btor2BinaryOperation, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2TernaryOperation, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2SliceOperation, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2ExtOperation, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Const, param: ParamPack): ParamPack {
        // TODO I will have to think more about what variables will be global in the end
        val constVar = node.getVar()
        param.builder.addVar(constVar)
        val newLoc = XcfaLocation("const_node_loc_"+node.nid)
        param.builder.addLoc(newLoc)
        param.builder.addEdge(XcfaEdge(param.lastLoc, newLoc,
                                StmtLabel(Stmts.Assign(
                                    constVar,
                                    BvUtils.bigIntegerToNeutralBvLitExpr(node.value, node.sort.width.toInt())
        ), metadata = EmptyMetaData)))
        return ParamPack(param.builder, newLoc)
    }

    override fun visit(node: Btor2BvSort, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Input, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2State, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Init, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Next, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Bad, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Constraint, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Output, param: ParamPack): ParamPack {
        TODO("Not yet implemented")
    }
}

class ParamPack(builder: XcfaProcedureBuilder, lastLoc: XcfaLocation) {
    val builder: XcfaProcedureBuilder
    val lastLoc: XcfaLocation

    init {
        this.builder = builder
        this.lastLoc = lastLoc
    }
}