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

import Btor2Sort
import hu.bme.mit.theta.core.type.arraytype.*
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.frontend.model.*
import hu.bme.mit.theta.frontend.model.Btor2NodeVisitor
import hu.bme.mit.theta.frontend.transformation.model.statements.*
import hu.bme.mit.theta.xcfa.model.*
import java.util.*
import kotlin.collections.LinkedHashSet

class Btor2FrontendXcfaBuilder(val sorts : HashMap<UInt, Btor2Sort>, val nodes : HashMap<UInt, Btor2Node>) :
    Btor2NodeVisitor<XcfaLocation> {
    private val locationLut: MutableMap<Btor2Node, XcfaLocation> = LinkedHashMap()
    private val visitedNodes = LinkedHashSet<Btor2Node>()

    fun buildXcfa(): XcfaBuilder {
        val builder = XcfaBuilder("TODO")

        for (node in nodes.values) {
            if (!visitedNodes.contains(node)) {
                node.accept(this)
                visitedNodes.add(node)
            } else {

            }
        }
    }

    override fun visit(node: Btor2UnaryOperation): XcfaLocation {
        val opd = node.operand
        val op = node.operator

        if (!visitedNodes.contains(opd)) {
            XcfaLocation = node.accept(this)
        } else {

        }
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2BinaryOperation): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2TernaryOperation): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2SliceOperation): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2ExtOperation): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Const): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Output): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Constraint): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Bad): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Next): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Init): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2State): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2Input): XcfaLocation {
        TODO("Not yet implemented")
    }

    override fun visit(node: Btor2BvSort): XcfaLocation {
        TODO("Not yet implemented")
    }

}