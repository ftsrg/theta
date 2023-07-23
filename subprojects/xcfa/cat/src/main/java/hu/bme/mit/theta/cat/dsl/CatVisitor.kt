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
package hu.bme.mit.theta.cat.dsl

import com.google.common.base.Preconditions
import hu.bme.mit.theta.cat.dsl.gen.CatBaseVisitor
import hu.bme.mit.theta.cat.dsl.gen.CatParser
import hu.bme.mit.theta.cat.dsl.gen.CatParser.*
import hu.bme.mit.theta.graphsolver.patterns.constraints.*
import hu.bme.mit.theta.graphsolver.patterns.patterns.*
import java.io.File
import java.io.FileNotFoundException
import java.io.IOException

class CatVisitor(file: File) : CatBaseVisitor<GraphPattern>() {

    private var mcm: MutableList<GraphConstraint>? = null
    private val ruleNameCnt = 0
    private val file: File
    private val relations: MutableMap<String, GraphPattern>
    private val functions: MutableMap<String, FunctionDefContext>
    private val procedures: MutableMap<String, ProcDefContext>
    private val paramAssignment: MutableMap<String, GraphPattern>

    init {
        relations = LinkedHashMap()
        procedures = LinkedHashMap()
        functions = LinkedHashMap()
        paramAssignment = LinkedHashMap()
        this.file = file
    }

    fun getMcm(): Collection<GraphConstraint>? {
        return mcm
    }

    private fun getOrCreateRelation(name: String, arity: Int): GraphPattern? {
        if (paramAssignment.containsKey(name)) {
            return paramAssignment[name]
        }
        if (relations.containsKey(name)) {
            return relations[name]
        }
        return if (arity == 1) BasicEventSet(name) else BasicRelation(name)
    }

    override fun visitMcm(ctx: McmContext): GraphPattern {
        mcm = ArrayList()
        val file = File(file.parent + File.separator + "stdlib.cat")
        visitIncludedFile(file)
        return super.visitMcm(ctx) ?: EmptyRel
    }

    private fun visitIncludedFile(file: File) {
        if (file.exists() && file.isFile) {
            try {
                val context = CatDslManager.setupCatAntlr(file)
                context.scopeBody().accept(this)
            } catch (e: IOException) {
                e.printStackTrace()
            }
        } else throw RuntimeException(FileNotFoundException(file.absolutePath))
    }

    override fun visitIncludeFile(ctx: IncludeFileContext): GraphPattern {
        val file = File(file.parent + File.separator + ctx.file.text)
        visitIncludedFile(file)
        return EmptyRel
    }

    override fun visitAcyclicDefinition(ctx: AcyclicDefinitionContext): GraphPattern {
        val rule = ctx.e.accept(this) as EdgePattern
        mcm!!.add(if (ctx.negate == null) Acyclic(rule) else Cyclic(rule))
        return EmptyRel
    }

    override fun visitIrreflexiveDefinition(ctx: IrreflexiveDefinitionContext): GraphPattern {
        val rule = ctx.e.accept(this) as EdgePattern
        mcm!!.add(if (ctx.negate == null) Irreflexive(rule) else Reflexive(rule))
        return EmptyRel
    }

    override fun visitEmptyDefinition(ctx: EmptyDefinitionContext): GraphPattern {
        val rule = ctx.e.accept(this)
        mcm!!.add(if (ctx.negate == null) Empty(rule) else Nonempty(rule))
        return EmptyRel
    }

    override fun visitFunctionDef(ctx: FunctionDefContext): GraphPattern {
        functions[ctx.n.text] = ctx
        return EmptyRel
    }

    override fun visitProcDef(ctx: ProcDefContext): GraphPattern {
        procedures[ctx.n.text] = ctx
        return EmptyRel
    }

    override fun visitExprToid(ctx: ExprToidContext): GraphPattern {
        val rel = ctx.e.accept(this) as NodePattern
        return Toid(rel)
    }

    override fun visitExprRange(ctx: ExprRangeContext): GraphPattern {
        val rel = ctx.e.accept(this) as EdgePattern
        return Range(rel)
    }

    override fun visitExprDomain(ctx: ExprDomainContext): GraphPattern {
        val rel = ctx.e.accept(this) as EdgePattern
        return Domain(rel)
    }

    override fun visitProcCall(ctx: ProcCallContext): GraphPattern {
        val procDefContext = procedures[ctx.NAME().text]
        Preconditions.checkNotNull(procDefContext, "Procedure with name " + ctx.NAME().text + " does not exist.")
        val e = ctx.params
        val toReset: MutableMap<String, GraphPattern?> = LinkedHashMap()
        for (i in e.indices) {
            val text = procDefContext!!.params[i].text
            val expressionContext = e[i]
            toReset[text] = paramAssignment[text]
            paramAssignment[text] = expressionContext.accept(this)
        }
        val accept = procDefContext!!.body.accept(this)
        toReset.forEach { (s: String, graphPattern: GraphPattern?) ->
            if (graphPattern == null) paramAssignment.remove(s) else paramAssignment[s] = graphPattern
        }
        return accept
    }

    override fun visitExprTryWith(ctx: ExprTryWithContext): GraphPattern {
        return ctx.e.accept(this)
    }

    override fun visitExprFunctionCall(ctx: ExprFunctionCallContext): GraphPattern {
        val functionDefContext = functions[ctx.NAME().text]
        Preconditions.checkNotNull(functionDefContext, "Function with name " + ctx.NAME().text + " does not exist.")
        val e = ctx.e
        val toReset: MutableMap<String, GraphPattern?> = LinkedHashMap()
        for (i in e.indices) {
            val text = functionDefContext!!.params[i].text
            val expressionContext = e[i]
            toReset[text] = paramAssignment[text]
            paramAssignment[text] = expressionContext.accept(this)
        }
        val accept = functionDefContext!!.e.accept(this)
        toReset.forEach { (s: String, graphPattern: GraphPattern?) ->
            if (graphPattern == null) paramAssignment.remove(s) else paramAssignment[s] = graphPattern
        }
        return accept
    }

    override fun visitLetDefinition(ctx: LetDefinitionContext): GraphPattern {
        var name = ctx.NAME().text
        var eCtx = ctx.e
        relations.remove(name)
        for (letAndDefinitionContext in ctx.letAndDefinition()) {
            name = letAndDefinitionContext.NAME().text
            relations.remove(name)
        }
        var rel = eCtx.accept(this)
        rel.patternName = ctx.NAME().text
        relations[ctx.NAME().text] = rel
        for (letAndDefinitionContext in ctx.letAndDefinition()) {
            name = letAndDefinitionContext.NAME().text
            eCtx = letAndDefinitionContext.e
            rel = eCtx.accept(this)
            relations[name] = rel
        }
        return rel
    }

    override fun visitExprCartesian(ctx: ExprCartesianContext): GraphPattern {
        val rel1 = ctx.e1.accept(this) as NodePattern
        val rel2 = ctx.e2.accept(this) as NodePattern
        return CartesianProduct(rel1, rel2)
    }

    override fun visitExprBasic(ctx: ExprBasicContext): GraphPattern {
        return getOrCreateRelation(ctx.NAME().text, if (Character.isLowerCase(ctx.NAME().text[0])) 2 else 1)!!
    }

    override fun visitExprMinus(ctx: ExprMinusContext): GraphPattern {
        val rel1 = ctx.e1.accept(this)
        val rel2 = ctx.e2.accept(this)
        return if (rel1 is EdgePattern && rel2 is EdgePattern)
            Difference(rel1, rel2)
        else if (rel1 is NodePattern && rel2 is NodePattern)
            DifferenceNode(rel1, rel2)
        else error("Mismatched types")
    }

    override fun visitExprUnion(ctx: ExprUnionContext): GraphPattern {
        val rel1 = ctx.e1.accept(this)
        val rel2 = ctx.e2.accept(this)
        return if (rel1 is EdgePattern && rel2 is EdgePattern)
            Union(rel1, rel2)
        else if (rel1 is NodePattern && rel2 is NodePattern)
            UnionNode(rel1, rel2)
        else error("Mismatched types")
    }

    override fun visitExprComposition(ctx: ExprCompositionContext): GraphPattern {
        val rel1 = ctx.e1.accept(this) as EdgePattern
        val rel2 = ctx.e2.accept(this) as EdgePattern
        return Sequence(rel1, rel2)
    }

    override fun visitExprIntersection(ctx: ExprIntersectionContext): GraphPattern {
        val rel1 = ctx.e1.accept(this)
        val rel2 = ctx.e2.accept(this)
        return if (rel1 is EdgePattern && rel2 is EdgePattern)
            Intersection(rel1, rel2)
        else if (rel1 is NodePattern && rel2 is NodePattern)
            IntersectionNode(rel1, rel2)
        else error("Mismatched types")
    }

    override fun visitExprTransitive(ctx: ExprTransitiveContext): GraphPattern {
        val rel = ctx.e.accept(this) as EdgePattern
        return TransitiveClosure(rel)
    }

    override fun visitExprComplement(ctx: ExprComplementContext): GraphPattern {
        val rel = ctx.e.accept(this)
        return if (rel is EdgePattern) Complement(rel) else if (rel is NodePattern) ComplementNode(rel) else error(
            "Mismatched types")
    }

    override fun visitExprInverse(ctx: ExprInverseContext): GraphPattern {
        val rel = ctx.e.accept(this) as EdgePattern
        return Inverse(rel)
    }

    override fun visitExprTransRef(ctx: ExprTransRefContext): GraphPattern {
        val rel = ctx.e.accept(this) as EdgePattern
        return ReflexiveTransitiveClosure(rel)
    }

    override fun visitExpr(ctx: CatParser.ExprContext): GraphPattern {
        return ctx.e.accept(this)
    }

    override fun visitExprOptional(ctx: ExprOptionalContext): GraphPattern {
        val rel = ctx.e.accept(this) as EdgePattern
        return IdentityClosure(rel)
    }

    override fun visitExprNull(ctx: ExprNullContext): GraphPattern {
        return EmptyRel
    }

    override fun toString(): String {
        return mcm.toString()
    }
}