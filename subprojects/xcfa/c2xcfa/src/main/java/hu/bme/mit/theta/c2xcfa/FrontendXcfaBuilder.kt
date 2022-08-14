/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
@file:Suppress("DuplicatedCode")

package hu.bme.mit.theta.c2xcfa

import com.google.common.base.Preconditions
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils
import hu.bme.mit.theta.frontend.FrontendMetadata
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Dereference
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Reference
import hu.bme.mit.theta.frontend.transformation.model.statements.*
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.CPasses
import java.util.*
import java.util.Set
import java.util.stream.Collectors
import kotlin.collections.ArrayList
import kotlin.collections.Collection
import kotlin.collections.LinkedHashMap
import kotlin.collections.LinkedHashSet
import kotlin.collections.List
import kotlin.collections.MutableCollection
import kotlin.collections.MutableList
import kotlin.collections.MutableMap
import kotlin.collections.listOf
import kotlin.collections.set

class FrontendXcfaBuilder : CStatementVisitorBase<FrontendXcfaBuilder.ParamPack, XcfaLocation>() {
    private val locationLut: MutableMap<String, XcfaLocation> = LinkedHashMap()
    private fun getLoc(builder: XcfaProcedureBuilder, name: String?): XcfaLocation {
        if (name == null) return getAnonymousLoc(builder)
        locationLut.putIfAbsent(name, XcfaLocation(name))
        val location = locationLut[name]
        builder.addLoc(location!!)
        return location
    }

    private fun getAnonymousLoc(builder: XcfaProcedureBuilder): XcfaLocation {
        return getLoc(builder, "__loc_" + XcfaLocation.uniqueCounter())
    }

    protected fun <T> propagateMetadata(source: CStatement?, newOwner: T) {
        FrontendMetadata.create(newOwner, "sourceStatement", source)
    }

    fun buildXcfa(cProgram: CProgram): XcfaBuilder {
        val builder = XcfaBuilder(cProgram.id ?: "")
        val initStmtList: MutableList<XcfaLabel> = ArrayList()
        for (globalDeclaration in cProgram.globalDeclarations) {
            val type = CComplexType.getType(globalDeclaration.get2().ref)
            if (type is CVoid || type is CStruct) {
                System.err.println("WARNING: Not handling init expression of " + globalDeclaration.get1() + " as it is non initializable")
                continue
            }
            builder.addVar(XcfaGlobalVar(globalDeclaration.get2(), type.nullValue))
            if (globalDeclaration.get1().initExpr != null) {
                initStmtList.add(StmtLabel(Stmts.Assign(TypeUtils.cast(globalDeclaration.get2(), globalDeclaration.get2().type), TypeUtils.cast(type.castTo(globalDeclaration.get1().initExpr.expression), globalDeclaration.get2().type))))
            } else {
                initStmtList.add(StmtLabel(Stmts.Assign(TypeUtils.cast(globalDeclaration.get2(), globalDeclaration.get2().type), TypeUtils.cast(type.nullValue, globalDeclaration.get2().type))))
            }
        }
        for (function in cProgram.functions) {
            val toAdd: XcfaProcedureBuilder = handleFunction(function, initStmtList)
            builder.addProcedure(toAdd)
            if (toAdd.name.equals("main")) builder.addEntryPoint(toAdd, listOf())
        }
        return builder
    }

    private fun handleFunction(function: CFunction, param: List<XcfaLabel>): XcfaProcedureBuilder {
        locationLut.clear()
        val flatVariables = function.flatVariables
        val funcDecl = function.funcDecl
        val compound = function.compound
        val builder = XcfaProcedureBuilder(funcDecl.name, CPasses())
        for (flatVariable in flatVariables) {
            builder.addVar(flatVariable)
        }
//        builder.setRetType(if (funcDecl.actualType is CVoid) null else funcDecl.actualType.smtType) TODO: we never need the ret type, do we?
        if (funcDecl.actualType !is CVoid) {
            val toAdd: VarDecl<*> = Decls.Var(funcDecl.name + "_ret", funcDecl.actualType.smtType)
            FrontendMetadata.create(toAdd.ref, "cType", funcDecl.actualType)
            builder.addParam(toAdd, ParamDirection.OUT)
        } else {
            // TODO we assume later that there is always a ret var, but this should change
            val toAdd: VarDecl<*> = Decls.Var(funcDecl.name + "_ret", funcDecl.actualType.smtType)
            val signedIntType = CSimpleTypeFactory.NamedType("int")
            signedIntType.setSigned(true)
            FrontendMetadata.create(toAdd.ref, "cType", signedIntType)
            builder.addParam(toAdd, ParamDirection.OUT)
        }
        for (functionParam in funcDecl.functionParams) {
            Preconditions.checkState(functionParam.actualType is CVoid || functionParam.varDecls.size > 0, "Function param should have an associated variable!")
            for (varDecl in functionParam.varDecls) {
                if (varDecl != null) builder.addParam(varDecl, ParamDirection.IN)
            }
        }
        builder.createInitLoc()
        propagateMetadata(function, builder.initLoc)
        var init = builder.initLoc
        if (param.size > 0 && builder.name.equals("main")) {
            val endinit = getAnonymousLoc(builder)
            builder.addLoc(endinit)
            propagateMetadata(function, endinit)
            val edge = XcfaEdge(init, endinit, SequenceLabel(param))
            builder.addEdge(edge)
            propagateMetadata(function, edge)
            init = endinit
        }
        builder.createFinalLoc()
        val ret = builder.finalLoc.get()
        builder.addLoc(ret)
        propagateMetadata(function, ret)
        val end = compound.accept(this, ParamPack(builder, init, null, null, ret))
        val edge = XcfaEdge(end, ret)
        builder.addEdge(edge)
        propagateMetadata(function, edge)
        return builder
    }

    override fun visit(statement: CAssignment, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val lValue = statement.getlValue()
        val rValue = statement.getrValue()
        val memoryMaps = CAssignment.getMemoryMaps()
        var initLoc = getLoc(builder, statement.id)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        var xcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val location = getAnonymousLoc(builder)
        builder.addLoc(location)
        propagateMetadata(statement, location)
        initLoc = rValue.accept(this, ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc))
        Preconditions.checkState(lValue is Dereference<*, *> || lValue is ArrayReadExpr<*, *> || lValue is RefExpr<*> && lValue.decl is VarDecl<*>, "lValue must be a variable, pointer dereference or an array element!")
        val rExpression = statement.getrExpression()
        if (lValue is ArrayReadExpr<*, *>) {
            val exprs = Stack<Expr<*>>()
            val toAdd = createArrayWriteExpr(lValue as ArrayReadExpr<*, out Type>, rExpression, exprs)
            xcfaEdge = XcfaEdge(initLoc, location, StmtLabel(Stmts.Assign(TypeUtils.cast(toAdd, toAdd.type), TypeUtils.cast(exprs.pop(), toAdd.type))))
            builder.addEdge(xcfaEdge)
            propagateMetadata(statement, xcfaEdge)
        } else if (lValue is Dereference<*, *>) {
            val op = lValue.op
            val type = op.type
            val ptrType = CComplexType.getUnsignedLong().smtType
            if (!memoryMaps.containsKey(type)) {
                val toAdd = Decls.Var<ArrayType<*, *>>("memory_$type", ArrayType.of(ptrType, type))
                memoryMaps[type] = toAdd
                FrontendMetadata.create(toAdd, "defaultElement", CComplexType.getType(op).nullValue)
            }
            val memoryMap = memoryMaps[type]!!
            FrontendMetadata.create(op, "dereferenced", true)
            FrontendMetadata.create(op, "refSubstitute", memoryMap)
            val write = ArrayExprs.Write(TypeUtils.cast(memoryMap.ref, ArrayType.of(ptrType, type)),
                    TypeUtils.cast(lValue.op, ptrType),
                    TypeUtils.cast(rExpression, type))
            FrontendMetadata.create(write, "cType", CArray(null, CComplexType.getType(lValue.op)))
            xcfaEdge = XcfaEdge(initLoc, location, StmtLabel(Stmts.Assign(TypeUtils.cast(memoryMap, ArrayType.of(ptrType, type)), write)))
            builder.addEdge(xcfaEdge)
            propagateMetadata(statement, xcfaEdge)
        } else {
            xcfaEdge = XcfaEdge(initLoc, location, StmtLabel(Stmts.Assign(
                    TypeUtils.cast((lValue as RefExpr<*>).decl as VarDecl<*>, (lValue.decl as VarDecl<*>).type),
                    TypeUtils.cast(CComplexType.getType(lValue).castTo(rExpression), lValue.type))))
            if (CComplexType.getType(lValue) is CPointer && CComplexType.getType(rExpression) is CPointer) {
                Preconditions.checkState(rExpression is RefExpr<*> || rExpression is Reference<*, *>)
                if (rExpression is RefExpr<*>) {
                    var pointsTo = FrontendMetadata.getMetadataValue(lValue, "pointsTo")
                    if (pointsTo.isPresent && pointsTo.get() is Collection<*>) {
                        (pointsTo.get() as MutableCollection<Expr<*>?>).add(rExpression)
                    } else {
                        pointsTo = Optional.of(LinkedHashSet<Expr<*>>(Set.of(rExpression)))
                    }
                    FrontendMetadata.create(lValue, "pointsTo", pointsTo.get())
                } else {
                    var pointsTo = FrontendMetadata.getMetadataValue(lValue, "pointsTo")
                    if (pointsTo.isPresent && pointsTo.get() is Collection<*>) {
                        (pointsTo.get() as MutableCollection<Expr<*>?>).add((rExpression as Reference<*, *>).op)
                    } else {
                        pointsTo = Optional.of(LinkedHashSet(Set.of((rExpression as Reference<*, *>).op)))
                    }
                    FrontendMetadata.create(lValue, "pointsTo", pointsTo.get())
                }
            }
            builder.addEdge(xcfaEdge)
            propagateMetadata(statement, xcfaEdge)
        }
        return location
    }

    private fun <P : Type?, T : Type?> createArrayWriteExpr(lValue: ArrayReadExpr<P, T>, rExpression: Expr<*>, exprs: Stack<Expr<*>>): VarDecl<*> {
        val array = lValue.array
        val index = lValue.index
        val arrType = CComplexType.getType(array)
        check(arrType is CArray)
        arrType.embeddedType.castTo(rExpression)
        val arrayWriteExpr = ArrayWriteExpr.of(array, index, TypeUtils.cast(rExpression, array.type.elemType))
        FrontendMetadata.create(arrayWriteExpr, "cType", arrType)
        return if (array is RefExpr<*> && (array as RefExpr<ArrayType<P, T>>).decl is VarDecl<*>) {
            exprs.push(arrayWriteExpr)
            array.decl as VarDecl<*>
        } else if (array is ArrayReadExpr<*, *>) {
            createArrayWriteExpr(array as ArrayReadExpr<P, *>, arrayWriteExpr, exprs)
        } else throw UnsupportedOperationException("Possible malformed array write?")
    }

    override fun visit(statement: CAssume, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val initLoc = getLoc(builder, statement.id)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val location = getAnonymousLoc(builder)
        builder.addLoc(location)
        propagateMetadata(statement, location)
        xcfaEdge = XcfaEdge(initLoc, location, StmtLabel(statement.assumeStmt))
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        return location
    }

    override fun visit(statement: CBreak, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val initLoc = getLoc(builder, statement.id)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        var edge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(edge)
        propagateMetadata(statement, edge)
        check(breakLoc != null)
        edge = XcfaEdge(initLoc, breakLoc)
        val unreachableLoc: XcfaLocation = XcfaLocation("Unreachable" + XcfaLocation.uniqueCounter())
        builder.addLoc(unreachableLoc)
        propagateMetadata(statement, unreachableLoc)
        builder.addEdge(edge)
        propagateMetadata(statement, edge)
        return unreachableLoc
    }

    override fun visit(statement: CCall, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val ret = statement.ret
        val myParams = statement.params
        var initLoc = getLoc(builder, statement.id)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val location = getAnonymousLoc(builder)
        builder.addLoc(location)
        propagateMetadata(statement, location)
        val params: MutableList<Expr<*>> = ArrayList()
        builder.addVar(ret)
        params.add(ret.ref)
        for (cStatement in myParams) {
            initLoc = cStatement.accept(this, ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc))
        }
        params.addAll(myParams.stream().map { obj: CStatement -> obj.expression }.collect(Collectors.toList()))
        val call = InvokeLabel(statement.functionId, params)
        propagateMetadata<Any>(statement, call)
        xcfaEdge = XcfaEdge(initLoc, location, call)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        return location
    }

    override fun visit(statement: CCase, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        return statement.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
    }

    override fun visit(statement: CCompound, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        var lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val preStatements = statement.preStatements
        val postStatements = statement.postStatements
        val initLoc = getLoc(builder, statement.id)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        val edge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(edge)
        propagateMetadata(statement, edge)
        lastLoc = initLoc
        if (preStatements != null) lastLoc = preStatements.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
        for (cStatement in statement.getcStatementList()) {
            if (cStatement != null) lastLoc = cStatement.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
        }
        if (postStatements != null) lastLoc = postStatements.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
        return lastLoc
    }

    override fun visit(statement: CContinue, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val initLoc = getLoc(builder, statement.id)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        var edge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(edge)
        propagateMetadata(statement, edge)
        check(continueLoc != null)
        edge = XcfaEdge(initLoc, continueLoc)
        val unreachableLoc: XcfaLocation = XcfaLocation("Unreachable" + XcfaLocation.uniqueCounter())
        builder.addLoc(unreachableLoc)
        propagateMetadata(statement, unreachableLoc)
        builder.addEdge(edge)
        propagateMetadata(statement, edge)
        return unreachableLoc
    }

    override fun visit(statement: CDefault, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        return statement.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
    }

    override fun visit(statement: CDoWhile, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val body = statement.body
        val guard = statement.guard
        val initLoc = getLoc(builder, statement.id)
        val endLoc = getAnonymousLoc(builder)
        val innerEndLoc = getAnonymousLoc(builder)
        val innerInnerGuard = getAnonymousLoc(builder)
        val outerInnerGuard = getAnonymousLoc(builder)
        builder.addLoc(endLoc)
        propagateMetadata(statement, endLoc)
        builder.addLoc(innerInnerGuard)
        propagateMetadata(statement, innerInnerGuard)
        builder.addLoc(outerInnerGuard)
        propagateMetadata(statement, outerInnerGuard)
        builder.addLoc(innerEndLoc)
        propagateMetadata(statement, innerEndLoc)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val lastBody = body.accept(this, ParamPack(builder, initLoc, endLoc, innerEndLoc, returnLoc))
        xcfaEdge = XcfaEdge(lastBody, innerEndLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val lastPre = buildWithoutPostStatement(guard, ParamPack(builder, innerEndLoc, null, null, returnLoc))
        val assume = Stmts.Assume(AbstractExprs.Neq(guard.expression, CComplexType.getType(guard.expression).nullValue))
        propagateMetadata(guard, assume)
        check(lastPre != null)
        xcfaEdge = XcfaEdge(lastPre, innerInnerGuard, StmtLabel(assume))
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val assume1 = Stmts.Assume(AbstractExprs.Eq(guard.expression, CComplexType.getType(guard.expression).nullValue))
        propagateMetadata(guard, assume1)
        xcfaEdge = XcfaEdge(lastPre, outerInnerGuard, StmtLabel(assume1))
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val outerLastGuard = buildPostStatement(guard, ParamPack(builder, outerInnerGuard, null, null, null))
        val innerLastGuard = buildPostStatement(guard, ParamPack(builder, innerInnerGuard, null, null, null))
        xcfaEdge = XcfaEdge(outerLastGuard, endLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        xcfaEdge = XcfaEdge(innerLastGuard, initLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        return endLoc
    }

    override fun visit(statement: CExpr, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        return lastLoc
    }

    override fun visit(statement: CFor, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val increment = statement.increment
        val init = statement.init
        val guard = statement.guard
        val body = statement.body
        val initLoc = getLoc(builder, statement.id)
        val endLoc = getAnonymousLoc(builder)
        val endInit = getAnonymousLoc(builder)
        val startIncrement = getAnonymousLoc(builder)
        val outerLastTest = getAnonymousLoc(builder)
        builder.addLoc(endLoc)
        propagateMetadata(statement, endLoc)
        builder.addLoc(outerLastTest)
        propagateMetadata(statement, outerLastTest)
        builder.addLoc(endInit)
        propagateMetadata(statement, endInit)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        builder.addLoc(startIncrement)
        propagateMetadata(statement, startIncrement)
        var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val lastInit = if (init == null) initLoc else init.accept(this, ParamPack(builder, initLoc, null, null, returnLoc))
        val lastTest = if (guard == null) lastInit else buildWithoutPostStatement(guard, ParamPack(builder, lastInit!!, null, null, returnLoc))
        val assume = Stmts.Assume(AbstractExprs.Neq(guard!!.expression, CComplexType.getType(guard.expression).nullValue))
        propagateMetadata(guard, assume)
        check(lastTest != null)
        xcfaEdge = XcfaEdge(lastTest, endInit, StmtLabel(assume))
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val assume1 = Stmts.Assume(AbstractExprs.Eq(guard.expression, CComplexType.getType(guard.expression).nullValue))
        propagateMetadata(guard, assume1)
        xcfaEdge = XcfaEdge(lastTest, outerLastTest, StmtLabel(assume1))
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val innerLastGuard = buildPostStatement(guard, ParamPack(builder, endInit, endLoc, startIncrement, returnLoc))
        val lastBody = if (body == null) innerLastGuard else body.accept(this, ParamPack(builder, innerLastGuard, endLoc, startIncrement, returnLoc))
        xcfaEdge = XcfaEdge(lastBody, startIncrement)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        if (increment != null) {
            val lastIncrement = increment.accept(this, ParamPack(builder, startIncrement, null, null, returnLoc))
            xcfaEdge = XcfaEdge(lastIncrement, lastInit)
            builder.addEdge(xcfaEdge)
            propagateMetadata(statement, xcfaEdge)
        } else {
            xcfaEdge = XcfaEdge(startIncrement, lastInit)
            builder.addEdge(xcfaEdge)
            propagateMetadata(statement, xcfaEdge)
        }
        val outerLastGuard = buildPostStatement(guard, ParamPack(builder, outerLastTest, endLoc, startIncrement, returnLoc))
        xcfaEdge = XcfaEdge(outerLastGuard, endLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        return endLoc
    }

    override fun visit(statement: CGoto, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val initLoc = getLoc(builder, statement.id)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        var edge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(edge)
        propagateMetadata(statement, edge)
        edge = XcfaEdge(initLoc, getLoc(builder, statement.label))
        builder.addLoc(getLoc(builder, statement.label))
        val unreachableLoc: XcfaLocation = XcfaLocation("Unreachable" + XcfaLocation.uniqueCounter())
        builder.addLoc(unreachableLoc)
        propagateMetadata(statement, unreachableLoc)
        builder.addEdge(edge)
        propagateMetadata(statement, edge)
        return unreachableLoc
    }

    override fun visit(statement: CIf, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val elseStatement = statement.elseStatement
        val body = statement.body
        val guard = statement.guard
        val initLoc = getLoc(builder, statement.id)
        val endLoc = getAnonymousLoc(builder)
        val mainBranch = getAnonymousLoc(builder)
        val elseBranch = getAnonymousLoc(builder)
        builder.addLoc(endLoc)
        propagateMetadata(statement, endLoc)
        builder.addLoc(mainBranch)
        propagateMetadata(statement, mainBranch)
        builder.addLoc(elseBranch)
        propagateMetadata(statement, elseBranch)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val endGuard = buildWithoutPostStatement(guard, ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc))
        val assume = Stmts.Assume(AbstractExprs.Neq(guard.expression, CComplexType.getType(guard.expression).nullValue))
        propagateMetadata(guard, assume)
        check(endGuard != null)
        xcfaEdge = XcfaEdge(endGuard, mainBranch, StmtLabel(assume))
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val assume1 = Stmts.Assume(AbstractExprs.Eq(guard.expression, CComplexType.getType(guard.expression).nullValue))
        propagateMetadata(guard, assume1)
        xcfaEdge = XcfaEdge(endGuard, elseBranch, StmtLabel(assume1))
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val mainAfterGuard = buildPostStatement(guard, ParamPack(builder, mainBranch, breakLoc, continueLoc, returnLoc))
        val mainEnd = body.accept(this, ParamPack(builder, mainAfterGuard, breakLoc, continueLoc, returnLoc))
        if (elseStatement != null) {
            val elseAfterGuard = buildPostStatement(guard, ParamPack(builder, elseBranch, breakLoc, continueLoc, returnLoc))
            val elseEnd = elseStatement.accept(this, ParamPack(builder, elseAfterGuard, breakLoc, continueLoc, returnLoc))
            xcfaEdge = XcfaEdge(elseEnd, endLoc)
            builder.addEdge(xcfaEdge)
            propagateMetadata(statement, xcfaEdge)
        } else {
            xcfaEdge = XcfaEdge(elseBranch, endLoc)
            builder.addEdge(xcfaEdge)
            propagateMetadata(statement, xcfaEdge)
        }
        xcfaEdge = XcfaEdge(mainEnd, endLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        return endLoc
    }

    override fun visit(statement: CInitializerList, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        var lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        for (cStatement in statement.statements) {
            lastLoc = cStatement.get2().accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
        }
        return lastLoc
    }

    override fun visit(statement: CRet, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val expr = statement.expr ?: return lastLoc
        val initLoc = getLoc(builder, statement.id)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        val xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val endExpr = expr.accept(this, ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc))
        val endLoc = getAnonymousLoc(builder)
        builder.addLoc(endLoc)
        propagateMetadata(statement, endLoc)
        val key: VarDecl<*> = builder.getParams()[0].first
        check(returnLoc != null)
        val edge = XcfaEdge(endExpr, returnLoc, StmtLabel(Stmts.Assign(TypeUtils.cast(key, key.type), TypeUtils.cast(CComplexType.getType(key.ref).castTo(expr.expression), key.type))))
        builder.addEdge(edge)
        propagateMetadata(statement, edge)
        return endLoc
    }

    override fun visit(statement: CSwitch, param: ParamPack): XcfaLocation {
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val testValue = statement.testValue
        val body = statement.body
        val initLoc = getLoc(builder, statement.id)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        val endLoc = getAnonymousLoc(builder)
        builder.addLoc(endLoc)
        propagateMetadata(statement, endLoc)
        val edge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(edge)
        propagateMetadata(statement, edge)
        val endInit = buildWithoutPostStatement(testValue, ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc))
        Preconditions.checkState(body is CCompound, "Switch body has to be a CompoundStatement!")
        var defaultExpr: Expr<BoolType?>? = BoolExprs.True()
        for (cStatement in (body as CCompound).getcStatementList()) {
            if (cStatement is CCase) {
                defaultExpr = BoolExprs.And(defaultExpr, AbstractExprs.Neq(testValue.expression, cStatement.expr.expression))
            }
        }
        var lastLocation: XcfaLocation? = null
        for (cStatement in body.getcStatementList()) {
            val location = getAnonymousLoc(builder)
            builder.addLoc(location)
            propagateMetadata(statement, location)
            var xcfaEdge: XcfaEdge
            if (lastLocation != null) {
                xcfaEdge = XcfaEdge(lastLocation, location)
                builder.addEdge(xcfaEdge)
                propagateMetadata(statement, xcfaEdge)
            }
            if (cStatement is CCase) {
                val afterGuard = buildPostStatement(testValue, ParamPack(builder, endInit!!, breakLoc, continueLoc, returnLoc))
                val assume = Stmts.Assume(AbstractExprs.Eq(testValue.expression, cStatement.expr.expression))
                propagateMetadata(statement, assume)
                xcfaEdge = XcfaEdge(afterGuard, location, StmtLabel(assume))
                builder.addEdge(xcfaEdge)
                propagateMetadata(statement, xcfaEdge)
            } else if (cStatement is CDefault) {
                val afterGuard = buildPostStatement(testValue, ParamPack(builder, endInit!!, breakLoc, continueLoc, returnLoc))
                val assume = Stmts.Assume(defaultExpr)
                propagateMetadata(statement, assume)
                xcfaEdge = XcfaEdge(afterGuard, location, StmtLabel(assume))
                builder.addEdge(xcfaEdge)
                propagateMetadata(statement, xcfaEdge)
            }
            lastLocation = cStatement.accept(this, ParamPack(builder, location, endLoc, continueLoc, returnLoc))
        }
        if (lastLocation != null) {
            val xcfaEdge: XcfaEdge = XcfaEdge(lastLocation, endLoc)
            builder.addEdge(xcfaEdge)
            propagateMetadata(statement, xcfaEdge)
        }
        return endLoc
    }

    override fun visit(statement: CWhile, param: ParamPack): XcfaLocation {
        val UNROLL_COUNT = 0
        val builder: XcfaProcedureBuilder = param.builder
        val lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val guard = statement.guard
        val body = statement.body
        var initLoc = getLoc(builder, statement.id)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        val endLoc = getAnonymousLoc(builder)
        builder.addLoc(endLoc)
        propagateMetadata(statement, endLoc)
        val outerBeforeGuard = getAnonymousLoc(builder)
        builder.addLoc(outerBeforeGuard)
        propagateMetadata(statement, outerBeforeGuard)
        for (i in 0 until if (UNROLL_COUNT == 0) 1 else UNROLL_COUNT) {
            val innerLoop = getAnonymousLoc(builder)
            builder.addLoc(innerLoop)
            propagateMetadata(statement, innerLoop)
            val testEndLoc = buildWithoutPostStatement(guard, ParamPack(builder, initLoc, null, null, returnLoc))
            if (UNROLL_COUNT > 0) {
                initLoc = getAnonymousLoc(builder)
                builder.addLoc(initLoc)
                propagateMetadata<XcfaLocation?>(statement, initLoc)
            }
            val assume = Stmts.Assume(AbstractExprs.Neq(guard.expression, CComplexType.getType(guard.expression).nullValue))
            propagateMetadata(guard, assume)
            check(testEndLoc != null)
            xcfaEdge = XcfaEdge(testEndLoc, innerLoop, StmtLabel(assume))
            builder.addEdge(xcfaEdge)
            propagateMetadata(statement, xcfaEdge)
            val assume1 = Stmts.Assume(AbstractExprs.Eq(guard.expression, CComplexType.getType(guard.expression).nullValue))
            propagateMetadata(guard, assume1)
            xcfaEdge = XcfaEdge(testEndLoc, outerBeforeGuard, StmtLabel(assume1))
            builder.addEdge(xcfaEdge)
            propagateMetadata(statement, xcfaEdge)
            val lastGuard = buildPostStatement(guard, ParamPack(builder, innerLoop, endLoc, initLoc, returnLoc))
            val lastBody = body.accept(this, ParamPack(builder, lastGuard, endLoc, initLoc, returnLoc))
            xcfaEdge = XcfaEdge(lastBody, initLoc)
            builder.addEdge(xcfaEdge)
            propagateMetadata(statement, xcfaEdge)
        }
        val outerLastGuard = buildPostStatement(guard, ParamPack(builder, outerBeforeGuard, null, null, null))
        xcfaEdge = XcfaEdge(outerLastGuard, endLoc)
        builder.addEdge(xcfaEdge)
        propagateMetadata(statement, xcfaEdge)
        return endLoc
    }

    private fun buildWithoutPostStatement(cStatement: CStatement, param: ParamPack): XcfaLocation {
        Preconditions.checkState(cStatement is CCompound, "Currently only CCompounds have pre- and post statements!")
        val statement = cStatement as CCompound
        val builder: XcfaProcedureBuilder = param.builder
        var lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val preStatements = statement.preStatements
        val postStatements = statement.postStatements
        val cStatementList = statement.getcStatementList()
        val initLoc = getLoc(builder, statement.id)
        builder.addLoc(initLoc)
        propagateMetadata(statement, initLoc)
        val edge = XcfaEdge(lastLoc, initLoc)
        builder.addEdge(edge)
        propagateMetadata(statement, edge)
        lastLoc = initLoc
        if (preStatements != null) lastLoc = preStatements.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
        for (i in 0 until cStatementList.size - 1) {
            val stmt = cStatementList[i]
            if (stmt != null) lastLoc = stmt.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
        }
        if (cStatementList.size == 0) return lastLoc
        val lastStatement = cStatementList[cStatementList.size - 1]
        lastLoc = if (postStatements == null) {
            buildWithoutPostStatement(lastStatement, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
        } else {
            lastStatement.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
        }
        return lastLoc
    }

    private fun buildPostStatement(cStatement: CStatement, param: ParamPack): XcfaLocation {
        Preconditions.checkState(cStatement is CCompound, "Currently only CCompounds have pre- and post statements!")
        val statement = cStatement as CCompound
        val builder: XcfaProcedureBuilder = param.builder
        var lastLoc = param.lastLoc
        val breakLoc = param.breakLoc
        val continueLoc = param.continueLoc
        val returnLoc = param.returnLoc
        val preStatements = statement.preStatements
        val postStatements = statement.postStatements
        val cStatementList = statement.getcStatementList()
        lastLoc = if (postStatements != null) postStatements.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc)) else buildPostStatement(cStatementList[cStatementList.size - 1], ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
        return lastLoc
    }

    class ParamPack(builder: XcfaProcedureBuilder, lastLoc: XcfaLocation, breakLoc: XcfaLocation?, continueLoc: XcfaLocation?, returnLoc: XcfaLocation?) {
        val builder: XcfaProcedureBuilder
        val lastLoc: XcfaLocation
        val breakLoc: XcfaLocation?
        val continueLoc: XcfaLocation?
        val returnLoc: XcfaLocation?

        init {
            this.builder = builder
            this.lastLoc = lastLoc
            this.breakLoc = breakLoc
            this.continueLoc = continueLoc
            this.returnLoc = returnLoc
        }
    }
}