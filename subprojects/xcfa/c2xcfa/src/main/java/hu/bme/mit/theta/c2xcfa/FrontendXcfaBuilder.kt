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
@file:Suppress("DuplicatedCode")

package hu.bme.mit.theta.c2xcfa

import com.google.common.base.Preconditions
import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.DivExpr
import hu.bme.mit.theta.core.type.abstracttype.MulExpr
import hu.bme.mit.theta.core.type.abstracttype.SubExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer
import hu.bme.mit.theta.frontend.transformation.model.statements.*
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory
import hu.bme.mit.theta.xcfa.AssignStmtLabel
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.CPasses
import hu.bme.mit.theta.xcfa.passes.MemsafetyPass
import java.math.BigInteger
import java.util.stream.Collectors

class FrontendXcfaBuilder(
  val parseContext: ParseContext,
  val checkOverflow: Boolean = false,
  val uniqueWarningLogger: Logger,
) : CStatementVisitorBase<FrontendXcfaBuilder.ParamPack, XcfaLocation>() {

  private val locationLut: MutableMap<String, XcfaLocation> = LinkedHashMap()
  private var ptrCnt = 1 // counts up, uses 3k+1
    get() = field.also { field += 3 }

  private fun getLoc(
    builder: XcfaProcedureBuilder,
    name: String?,
    metadata: MetaData,
  ): XcfaLocation {
    if (name == null) return getAnonymousLoc(builder, metadata = metadata)
    locationLut.putIfAbsent(name, XcfaLocation(name, metadata = metadata))
    val location = locationLut[name]
    builder.addLoc(checkNotNull(location))
    return location
  }

  private fun getAnonymousLoc(builder: XcfaProcedureBuilder, metadata: MetaData): XcfaLocation {
    return getLoc(builder, "__loc_" + XcfaLocation.uniqueCounter(), metadata)
  }

  private fun getMetadata(source: CStatement): CMetaData =
    CMetaData(
      lineNumberStart = source.lineNumberStart.takeIf { it != -1 },
      lineNumberStop = source.lineNumberStop.takeIf { it != -1 },
      colNumberStart = source.colNumberStart.takeIf { it != -1 },
      colNumberStop = source.colNumberStop.takeIf { it != -1 },
      offsetStart = source.offsetStart.takeIf { it != -1 },
      offsetEnd = source.offsetEnd.takeIf { it != -1 },
      sourceText = source.sourceText,
    )

  fun buildXcfa(cProgram: CProgram): XcfaBuilder {
    val builder = XcfaBuilder(cProgram.id ?: "")
    val initStmtList: MutableList<XcfaLabel> = ArrayList()
    if (MemsafetyPass.NEED_CHECK) {
      val fitsall = Fitsall.getFitsall(parseContext)
      val ptrType = CPointer(null, null, parseContext)
      val ptrSize =
        XcfaGlobalVar(
          Var("__theta_ptr_size", ArrayType.of(ptrType.smtType, fitsall.smtType)),
          ArrayLitExpr.of(
            listOf(),
            fitsall.nullValue as Expr<Type>,
            ArrayType.of(ptrType.smtType as Type, fitsall.smtType as Type),
          ),
        )
      builder.addVar(ptrSize)
      initStmtList.add(
        AssignStmtLabel(
          ptrSize.wrappedVar,
          ArrayLitExpr.of(
            listOf(),
            fitsall.nullValue as Expr<Type>,
            ArrayType.of(ptrType.smtType as Type, fitsall.smtType as Type),
          ),
        )
      )
    }
    for (globalDeclaration in cProgram.globalDeclarations) {
      val type = CComplexType.getType(globalDeclaration.get2().ref, parseContext)
      if (type is CVoid) {
        continue
      }
      if (type is CStruct) {
        uniqueWarningLogger.write(
          Logger.Level.INFO,
          "Not handling init expression of struct array ${globalDeclaration.get1()}",
        )
      }
      builder.addVar(
        XcfaGlobalVar(
          globalDeclaration.get2(),
          type.nullValue,
          atomic = globalDeclaration.get1().type.isAtomic,
        )
      )
      if (type is CArray) {
        initStmtList.add(
          StmtLabel(
            Stmts.Assign(
              cast(globalDeclaration.get2(), globalDeclaration.get2().type),
              cast(type.getValue("$ptrCnt"), globalDeclaration.get2().type),
            )
          )
        )
        if (MemsafetyPass.NEED_CHECK) {
          val bounds = globalDeclaration.get1().arrayDimensions[0].expression
          checkState(
            bounds is IntLitExpr || bounds is BvLitExpr,
            "Only IntLit and BvLit expression expected here.",
          )
          initStmtList.add(builder.allocate(parseContext, globalDeclaration.get2().ref, bounds))
        }
      } else {
        if (
          globalDeclaration.get1().initExpr != null &&
            globalDeclaration.get1().initExpr.expression !is UnsupportedInitializer
        ) {
          initStmtList.add(
            StmtLabel(
              Stmts.Assign(
                cast(globalDeclaration.get2(), globalDeclaration.get2().type),
                cast(
                  type.castTo(globalDeclaration.get1().initExpr.expression),
                  globalDeclaration.get2().type,
                ),
              )
            )
          )
        } else {
          initStmtList.add(
            StmtLabel(
              Stmts.Assign(
                cast(globalDeclaration.get2(), globalDeclaration.get2().type),
                cast(type.nullValue, globalDeclaration.get2().type),
              )
            )
          )
        }
      }

      if (globalDeclaration.get1().arrayDimensions.size == 1) {
        val bounds =
          ExprUtils.simplify(
            CComplexType.getUnsignedLong(parseContext)
              .castTo(globalDeclaration.get1().arrayDimensions[0].expression)
          )
        checkState(
          bounds is IntLitExpr || bounds is BvLitExpr,
          "Only IntLit and BvLit expression expected here.",
        )
        val literalValue =
          if (bounds is IntLitExpr) bounds.value.toLong()
          else BvUtils.neutralBvLitExprToBigInteger(bounds as BvLitExpr).toLong()
        val literalToExpr = { x: Long ->
          if (bounds is IntLitExpr) IntLitExpr.of(BigInteger.valueOf(x))
          else
            BvUtils.bigIntegerToNeutralBvLitExpr(
              BigInteger.valueOf(x),
              (bounds as BvLitExpr).type.size,
            )
        }
        val initExprs: Map<Int, Expr<*>> =
          (globalDeclaration.get1()?.initExpr as? CInitializerList)
            ?.statements
            ?.mapIndexed { i, it -> Pair(i, it.get2().expression) }
            ?.toMap() ?: emptyMap()
        for (i in 0 until literalValue) {
          checkState(globalDeclaration.get1().actualType is CArray, "Only arrays are expected here")
          val embeddedType = (globalDeclaration.get1().actualType as CArray).embeddedType
          initStmtList.add(
            StmtLabel(
              Stmts.MemoryAssign(
                Dereference(globalDeclaration.get2().ref, literalToExpr(i), embeddedType.smtType),
                cast(
                  initExprs[i.toInt()]?.let { embeddedType.castTo(it) } ?: embeddedType.nullValue,
                  embeddedType.smtType,
                ),
              )
            )
          )
        }
      } else if (globalDeclaration.get1().arrayDimensions.size > 1) {
        error("Not handling init expression of high dimsension array ${globalDeclaration.get1()}")
      }
    }
    for (function in cProgram.functions) {
      val toAdd: XcfaProcedureBuilder = handleFunction(function, initStmtList, builder)
      if (toAdd.name.equals("main")) builder.addEntryPoint(toAdd, listOf())
    }
    return builder
  }

  private fun handleFunction(
    function: CFunction,
    param: List<XcfaLabel>,
    xcfaBuilder: XcfaBuilder,
  ): XcfaProcedureBuilder {
    locationLut.clear()
    val flatVariables = function.flatVariables
    val isAtomic = function.atomicVariables::contains
    val funcDecl = function.funcDecl
    val compound = function.compound
    val builder =
      XcfaProcedureBuilder(funcDecl.name, CPasses(checkOverflow, parseContext, uniqueWarningLogger))
    xcfaBuilder.addProcedure(builder)
    val initStmtList = ArrayList<XcfaLabel>()
    if (param.size > 0 && builder.name.equals("main")) {
      initStmtList.addAll(param)
    }
    //        builder.setRetType(if (funcDecl.actualType is CVoid) null else
    // funcDecl.actualType.smtType) TODO: we never need the ret type, do we?
    if (funcDecl.actualType !is CVoid) {
      val toAdd: VarDecl<*> = Decls.Var(funcDecl.name + "_ret", funcDecl.actualType.smtType)
      parseContext.metadata.create(toAdd.ref, "cType", funcDecl.actualType)
      builder.addParam(toAdd, ParamDirection.OUT)
    } else {
      // TODO we assume later that there is always a ret var, but this should change
      val toAdd: VarDecl<*> = Decls.Var(funcDecl.name + "_ret", funcDecl.actualType.smtType)
      val signedIntType = CSimpleTypeFactory.NamedType("int", parseContext, uniqueWarningLogger)
      signedIntType.setSigned(true)
      parseContext.metadata.create(toAdd.ref, "cType", signedIntType)
      builder.addParam(toAdd, ParamDirection.OUT)
    }
    for (functionParam in funcDecl.functionParams) {
      Preconditions.checkState(
        functionParam.actualType is CVoid || functionParam.varDecls.size > 0,
        "Function param should have an associated variable!",
      )
      for (varDecl in functionParam.varDecls) {
        if (varDecl != null) builder.addParam(varDecl, ParamDirection.IN)
      }
    }

    for (flatVariable in flatVariables) {
      builder.addVar(flatVariable)
      if (isAtomic(flatVariable)) {
        builder.setAtomic(flatVariable)
      }
      val type = CComplexType.getType(flatVariable.ref, parseContext)
      if ((type is CStruct) && builder.getParams().none { it.first == flatVariable }) {
        initStmtList.add(
          StmtLabel(
            Stmts.Assign(
              cast(flatVariable, flatVariable.type),
              cast(type.getValue("$ptrCnt"), flatVariable.type),
            )
          )
        )
      }
    }
    builder.createInitLoc(getMetadata(function))
    var init = builder.initLoc

    for (flatVariable in flatVariables) {
      val type = CComplexType.getType(flatVariable.ref, parseContext)
      if (type is CArray && type.embeddedType is CArray) {
        // some day this is where initialization will occur. But this is not today.
        error("Not handling init expression of high dimsension array $flatVariable")
      }
    }

    val endinit = getAnonymousLoc(builder, getMetadata(function))
    builder.addLoc(endinit)
    val initEdge =
      XcfaEdge(init, endinit, SequenceLabel(initStmtList), metadata = getMetadata(function))
    builder.addEdge(initEdge)
    init = endinit
    builder.createFinalLoc(getMetadata(function))
    val ret = builder.finalLoc.get()
    builder.addLoc(ret)
    val end = compound.accept(this, ParamPack(builder, init, null, null, ret))
    val edge = XcfaEdge(end, ret, metadata = getMetadata(function))
    builder.addEdge(edge)
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
    var initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    var xcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val location = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(location)
    initLoc = rValue.accept(this, ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc))
    val rExpression = statement.getrExpression()
    val label: StmtLabel =
      when (lValue) {
        is Dereference<*, *, *> -> {
          val op = cast(lValue.array, lValue.array.type)
          val offset = cast(lValue.offset, op.type)
          val castRExpression = CComplexType.getType(lValue, parseContext).castTo(rExpression)
          val type = CComplexType.getType(castRExpression, parseContext)

          val deref = Dereference(op, offset, type.smtType)

          val memassign = MemoryAssignStmt.create(deref, castRExpression)

          parseContext.metadata.create(deref, "cType", CPointer(null, type, parseContext))
          StmtLabel(memassign, metadata = getMetadata(statement))
        }

        is RefExpr<*> -> {
          if (
            (CComplexType.getType(lValue, parseContext) is CPointer ||
              CComplexType.getType(lValue, parseContext) is CArray ||
              CComplexType.getType(lValue, parseContext) is CStruct) && rExpression.hasArithmetic()
          ) {
            throw UnsupportedFrontendElementException("Pointer arithmetic not supported.")
          }
          AssignStmtLabel(
            lValue,
            cast(CComplexType.getType(lValue, parseContext).castTo(rExpression), lValue.type),
            metadata = getMetadata(statement),
          )
        }

        else -> {
          error("Could not handle left-hand side of assignment $statement")
        }
      }

    val lhs = (label.stmt as? AssignStmt<*>)?.varDecl
    val type = lhs?.let { CComplexType.getType(it.ref, parseContext) }

    if (!checkOverflow || type == null || type !is CInteger || !type.isSsigned) {
      xcfaEdge = XcfaEdge(initLoc, location, label, metadata = getMetadata(statement))
      builder.addEdge(xcfaEdge)
    } else {
      lhs!!
      val middleLoc1 = getAnonymousLoc(builder, getMetadata(statement))
      val middleLoc2 = getAnonymousLoc(builder, getMetadata(statement))
      xcfaEdge = XcfaEdge(initLoc, middleLoc1, label, metadata = getMetadata(statement))
      builder.addEdge(xcfaEdge)

      xcfaEdge =
        XcfaEdge(
          middleLoc1,
          location,
          StmtLabel(type.limit(lhs.ref), metadata = getMetadata(statement)),
          metadata = getMetadata(statement),
        )
      builder.addEdge(xcfaEdge)
      xcfaEdge =
        XcfaEdge(
          middleLoc1,
          middleLoc2,
          StmtLabel(Assume(Not(type.limit(lhs.ref).cond)), metadata = getMetadata(statement)),
          metadata = getMetadata(statement),
        )
      builder.addEdge(xcfaEdge)
      xcfaEdge =
        XcfaEdge(
          middleLoc2,
          location,
          InvokeLabel("overflow", listOf(), metadata = getMetadata(statement)),
          metadata = getMetadata(statement),
        )
      builder.addEdge(xcfaEdge)
    }
    return location
  }

  override fun visit(statement: CAssume, param: ParamPack): XcfaLocation {
    val builder: XcfaProcedureBuilder = param.builder
    val lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    val initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val location = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(location)
    xcfaEdge =
      XcfaEdge(
        initLoc,
        location,
        StmtLabel(
          statement.assumeStmt,
          choiceType = ChoiceType.MAIN_PATH,
          metadata = getMetadata(statement),
        ),
        metadata = getMetadata(statement),
      )
    builder.addEdge(xcfaEdge)
    return location
  }

  override fun visit(statement: CBreak, param: ParamPack): XcfaLocation {
    val builder: XcfaProcedureBuilder = param.builder
    val lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    val initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    var edge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(edge)
    check(breakLoc != null)
    edge = XcfaEdge(initLoc, breakLoc, metadata = getMetadata(statement))
    val unreachableLoc =
      XcfaLocation("Unreachable" + XcfaLocation.uniqueCounter(), metadata = getMetadata(statement))
    builder.addLoc(unreachableLoc)
    builder.addEdge(edge)
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
    var initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val location = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(location)
    val params: MutableList<Expr<*>> = ArrayList()
    builder.addVar(ret)
    params.add(ret.ref)
    for (cStatement in myParams) {
      initLoc =
        cStatement.accept(this, ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc))
    }
    params.addAll(
      myParams.stream().map { obj: CStatement -> obj.expression }.collect(Collectors.toList())
    )
    val call = InvokeLabel(statement.functionId, params, metadata = getMetadata(statement))
    xcfaEdge = XcfaEdge(initLoc, location, call, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    return location
  }

  override fun visit(statement: CCase, param: ParamPack): XcfaLocation {
    val builder: XcfaProcedureBuilder = param.builder
    val lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    return statement.statement.accept(
      this,
      ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc),
    )
  }

  override fun visit(statement: CCompound, param: ParamPack): XcfaLocation {
    val builder: XcfaProcedureBuilder = param.builder
    var lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    val preStatements = statement.preStatements
    val postStatements = statement.postStatements
    val initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    val edge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(edge)
    lastLoc = initLoc
    if (preStatements != null)
      lastLoc =
        preStatements.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
    for (cStatement in statement.getcStatementList()) {
      if (cStatement != null)
        lastLoc =
          cStatement.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
    }
    if (postStatements != null)
      lastLoc =
        postStatements.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
    return lastLoc
  }

  override fun visit(statement: CContinue, param: ParamPack): XcfaLocation {
    val builder: XcfaProcedureBuilder = param.builder
    val lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    val initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    var edge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(edge)
    check(continueLoc != null)
    edge = XcfaEdge(initLoc, continueLoc, metadata = getMetadata(statement))
    val unreachableLoc: XcfaLocation =
      XcfaLocation("Unreachable" + XcfaLocation.uniqueCounter(), metadata = getMetadata(statement))
    builder.addLoc(unreachableLoc)
    builder.addEdge(edge)
    return unreachableLoc
  }

  override fun visit(statement: CDefault, param: ParamPack): XcfaLocation {
    val builder: XcfaProcedureBuilder = param.builder
    val lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    return statement.statement.accept(
      this,
      ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc),
    )
  }

  override fun visit(statement: CDoWhile, param: ParamPack): XcfaLocation {
    val builder: XcfaProcedureBuilder = param.builder
    val lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    val body = statement.body
    val guard = statement.guard
    val initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    val endLoc = getAnonymousLoc(builder, metadata = getMetadata(statement))
    val innerEndLoc = getAnonymousLoc(builder, metadata = getMetadata(statement))
    val innerInnerGuard = getAnonymousLoc(builder, metadata = getMetadata(statement))
    val outerInnerGuard = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(endLoc)
    builder.addLoc(innerInnerGuard)
    builder.addLoc(outerInnerGuard)
    builder.addLoc(innerEndLoc)
    builder.addLoc(initLoc)
    var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val lastBody = body.accept(this, ParamPack(builder, initLoc, endLoc, innerEndLoc, returnLoc))
    xcfaEdge = XcfaEdge(lastBody, innerEndLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val lastPre =
      buildWithoutPostStatement(guard, ParamPack(builder, innerEndLoc, null, null, returnLoc))
    val assume =
      StmtLabel(
        Stmts.Assume(
          AbstractExprs.Neq(
            guard.expression,
            CComplexType.getType(guard.expression, parseContext).nullValue,
          )
        ),
        choiceType = ChoiceType.MAIN_PATH,
        metadata = getMetadata(guard),
      )
    xcfaEdge = XcfaEdge(lastPre, innerInnerGuard, assume, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val assume1 =
      StmtLabel(
        Stmts.Assume(
          AbstractExprs.Eq(
            guard.expression,
            CComplexType.getType(guard.expression, parseContext).nullValue,
          )
        ),
        choiceType = ChoiceType.ALTERNATIVE_PATH,
        metadata = getMetadata(guard),
      )
    xcfaEdge = XcfaEdge(lastPre, outerInnerGuard, assume1, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val outerLastGuard =
      buildPostStatement(guard, ParamPack(builder, outerInnerGuard, null, null, null))
    val innerLastGuard =
      buildPostStatement(guard, ParamPack(builder, innerInnerGuard, null, null, null))
    xcfaEdge = XcfaEdge(outerLastGuard, endLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    xcfaEdge = XcfaEdge(innerLastGuard, initLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
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
    val initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    val endLoc = getAnonymousLoc(builder, metadata = getMetadata(statement))
    val endInit = getAnonymousLoc(builder, metadata = getMetadata(statement))
    val startIncrement = getAnonymousLoc(builder, metadata = getMetadata(statement))
    val outerLastTest = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(endLoc)
    builder.addLoc(outerLastTest)
    builder.addLoc(endInit)
    builder.addLoc(initLoc)
    builder.addLoc(startIncrement)
    var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val lastInit =
      if (init == null) initLoc
      else init.accept(this, ParamPack(builder, initLoc, null, null, returnLoc))
    val lastTest =
      if (guard == null) lastInit
      else buildWithoutPostStatement(guard, ParamPack(builder, lastInit!!, null, null, returnLoc))
    val assume =
      StmtLabel(
        Stmts.Assume(
          if (guard == null) True()
          else
            AbstractExprs.Neq(
              guard.expression,
              CComplexType.getType(guard.expression, parseContext).nullValue,
            )
        ),
        choiceType = ChoiceType.MAIN_PATH,
        metadata = if (guard == null) getMetadata(statement) else getMetadata(guard),
      )
    check(lastTest != null)
    xcfaEdge = XcfaEdge(lastTest, endInit, assume, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val assume1 =
      StmtLabel(
        Stmts.Assume(
          if (guard == null) False()
          else
            AbstractExprs.Eq(
              guard.expression,
              CComplexType.getType(guard.expression, parseContext).nullValue,
            )
        ),
        choiceType = ChoiceType.ALTERNATIVE_PATH,
        metadata = if (guard == null) getMetadata(statement) else getMetadata(guard),
      )
    xcfaEdge = XcfaEdge(lastTest, outerLastTest, assume1, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val innerLastGuard =
      if (guard == null) endInit
      else buildPostStatement(guard, ParamPack(builder, endInit, endLoc, startIncrement, returnLoc))
    val lastBody =
      if (body == null) innerLastGuard
      else body.accept(this, ParamPack(builder, innerLastGuard, endLoc, startIncrement, returnLoc))
    xcfaEdge = XcfaEdge(lastBody, startIncrement, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    if (increment != null) {
      val lastIncrement =
        increment.accept(this, ParamPack(builder, startIncrement, null, null, returnLoc))
      xcfaEdge = XcfaEdge(lastIncrement, lastInit, metadata = getMetadata(statement))
      builder.addEdge(xcfaEdge)
    } else {
      xcfaEdge = XcfaEdge(startIncrement, lastInit, metadata = getMetadata(statement))
      builder.addEdge(xcfaEdge)
    }
    val outerLastGuard =
      if (guard == null) outerLastTest
      else
        buildPostStatement(
          guard,
          ParamPack(builder, outerLastTest, endLoc, startIncrement, returnLoc),
        )
    xcfaEdge = XcfaEdge(outerLastGuard, endLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    return endLoc
  }

  override fun visit(statement: CGoto, param: ParamPack): XcfaLocation {
    val builder: XcfaProcedureBuilder = param.builder
    val lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    val initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    var edge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(edge)
    edge =
      XcfaEdge(
        initLoc,
        getLoc(builder, statement.label, metadata = getMetadata(statement)),
        metadata = getMetadata(statement),
      )
    builder.addLoc(getLoc(builder, statement.label, metadata = getMetadata(statement)))
    val unreachableLoc: XcfaLocation =
      XcfaLocation("Unreachable" + XcfaLocation.uniqueCounter(), metadata = getMetadata(statement))
    builder.addLoc(unreachableLoc)
    builder.addEdge(edge)
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
    val initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    val endLoc = getAnonymousLoc(builder, metadata = getMetadata(statement))
    val mainBranch = getAnonymousLoc(builder, metadata = getMetadata(statement))
    val elseBranch = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(endLoc)
    builder.addLoc(mainBranch)
    builder.addLoc(elseBranch)
    builder.addLoc(initLoc)
    var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val endGuard =
      buildWithoutPostStatement(
        guard,
        ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc),
      )
    val assume =
      StmtLabel(
        Stmts.Assume(
          AbstractExprs.Neq(
            guard.expression,
            CComplexType.getType(guard.expression, parseContext).nullValue,
          )
        ),
        choiceType = ChoiceType.MAIN_PATH,
        metadata = getMetadata(guard),
      )
    xcfaEdge = XcfaEdge(endGuard, mainBranch, assume, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val assume1 =
      StmtLabel(
        Stmts.Assume(
          AbstractExprs.Eq(
            guard.expression,
            CComplexType.getType(guard.expression, parseContext).nullValue,
          )
        ),
        choiceType = ChoiceType.ALTERNATIVE_PATH,
        metadata = getMetadata(guard),
      )
    xcfaEdge = XcfaEdge(endGuard, elseBranch, assume1, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val mainAfterGuard =
      buildPostStatement(guard, ParamPack(builder, mainBranch, breakLoc, continueLoc, returnLoc))
    val mainEnd =
      body.accept(this, ParamPack(builder, mainAfterGuard, breakLoc, continueLoc, returnLoc))
    if (elseStatement != null) {
      val elseAfterGuard =
        buildPostStatement(guard, ParamPack(builder, elseBranch, breakLoc, continueLoc, returnLoc))
      val elseEnd =
        elseStatement.accept(
          this,
          ParamPack(builder, elseAfterGuard, breakLoc, continueLoc, returnLoc),
        )
      xcfaEdge = XcfaEdge(elseEnd, endLoc, metadata = getMetadata(statement))
      builder.addEdge(xcfaEdge)
    } else {
      val elseAfterGuard =
        buildPostStatement(guard, ParamPack(builder, elseBranch, breakLoc, continueLoc, returnLoc))
      xcfaEdge = XcfaEdge(elseAfterGuard, endLoc, metadata = getMetadata(statement))
      builder.addEdge(xcfaEdge)
    }
    xcfaEdge = XcfaEdge(mainEnd, endLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    return endLoc
  }

  override fun visit(statement: CInitializerList, param: ParamPack): XcfaLocation {
    val builder: XcfaProcedureBuilder = param.builder
    var lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    for (cStatement in statement.statements) {
      lastLoc =
        cStatement
          .get2()
          .accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
    }
    return lastLoc
  }

  override fun visit(statement: CRet, param: ParamPack): XcfaLocation {
    val builder: XcfaProcedureBuilder = param.builder
    val lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    val expr = statement.expr
    val initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    val xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val endExpr =
      expr?.accept(this, ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc)) ?: initLoc
    val endLoc = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(endLoc)
    val key: VarDecl<*> = builder.getParams()[0].first
    check(returnLoc != null)
    val type = CComplexType.getType(key.ref, parseContext)
    val edge =
      XcfaEdge(
        endExpr,
        returnLoc,
        StmtLabel(
          Stmts.Assign(
            cast(key, key.type),
            cast(type.castTo(expr?.expression ?: type.nullValue), key.type),
          ),
          metadata = getMetadata(statement),
        ),
        metadata = getMetadata(statement),
      )
    builder.addEdge(edge)
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
    val initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    val endLoc = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(endLoc)
    val edge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(edge)
    val endInit =
      buildWithoutPostStatement(
        testValue,
        ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc),
      )
    Preconditions.checkState(body is CCompound, "Switch body has to be a CompoundStatement!")
    var defaultExpr: Expr<BoolType?>? = True()
    for (cStatement in (body as CCompound).getcStatementList()) {
      if (cStatement is CCase) {
        defaultExpr =
          BoolExprs.And(
            defaultExpr,
            AbstractExprs.Neq(testValue.expression, cStatement.expr.expression),
          )
      }
    }
    var lastLocation: XcfaLocation? = null
    for (cStatement in body.getcStatementList()) {
      val location = getAnonymousLoc(builder, metadata = getMetadata(statement))
      builder.addLoc(location)
      var xcfaEdge: XcfaEdge
      if (lastLocation != null) {
        xcfaEdge = XcfaEdge(lastLocation, location, metadata = getMetadata(statement))
        builder.addEdge(xcfaEdge)
      }
      if (cStatement is CCase) {
        val afterGuard =
          buildPostStatement(
            testValue,
            ParamPack(builder, checkNotNull(endInit), breakLoc, continueLoc, returnLoc),
          )
        val assume =
          StmtLabel(
            Stmts.Assume(AbstractExprs.Eq(testValue.expression, cStatement.expr.expression)),
            choiceType = ChoiceType.MAIN_PATH,
            metadata = getMetadata(testValue),
          )
        xcfaEdge = XcfaEdge(afterGuard, location, assume, metadata = getMetadata(statement))
        builder.addEdge(xcfaEdge)
      } else if (cStatement is CDefault) {
        val afterGuard =
          buildPostStatement(
            testValue,
            ParamPack(builder, endInit!!, breakLoc, continueLoc, returnLoc),
          )
        val assume =
          StmtLabel(
            Stmts.Assume(defaultExpr),
            choiceType = ChoiceType.MAIN_PATH, // TODO: is this what validators expect?
            metadata = getMetadata(cStatement),
          )
        xcfaEdge = XcfaEdge(afterGuard, location, assume, metadata = getMetadata(statement))
        builder.addEdge(xcfaEdge)
      }
      lastLocation =
        cStatement.accept(this, ParamPack(builder, location, endLoc, continueLoc, returnLoc))
    }
    if (lastLocation != null) {
      val xcfaEdge: XcfaEdge = XcfaEdge(lastLocation, endLoc, metadata = getMetadata(statement))
      builder.addEdge(xcfaEdge)
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
    var initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val endLoc = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(endLoc)
    val outerBeforeGuard = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(outerBeforeGuard)
    for (i in 0 until if (UNROLL_COUNT == 0) 1 else UNROLL_COUNT) {
      val innerLoop = getAnonymousLoc(builder, metadata = getMetadata(statement))
      builder.addLoc(innerLoop)
      val testEndLoc =
        buildWithoutPostStatement(guard, ParamPack(builder, initLoc, null, null, returnLoc))
      if (UNROLL_COUNT > 0) {
        initLoc = getAnonymousLoc(builder, metadata = getMetadata(statement))
        builder.addLoc(initLoc)
      }
      val assume =
        StmtLabel(
          Stmts.Assume(
            AbstractExprs.Neq(
              guard.expression,
              CComplexType.getType(guard.expression, parseContext).nullValue,
            )
          ),
          choiceType = ChoiceType.MAIN_PATH,
          metadata = getMetadata(guard),
        )
      xcfaEdge = XcfaEdge(testEndLoc, innerLoop, assume, metadata = getMetadata(statement))
      builder.addEdge(xcfaEdge)
      val assume1 =
        StmtLabel(
          Stmts.Assume(
            AbstractExprs.Eq(
              guard.expression,
              CComplexType.getType(guard.expression, parseContext).nullValue,
            )
          ),
          choiceType = ChoiceType.ALTERNATIVE_PATH,
          metadata = getMetadata(statement),
        )
      xcfaEdge = XcfaEdge(testEndLoc, outerBeforeGuard, assume1, metadata = getMetadata(statement))
      builder.addEdge(xcfaEdge)
      val lastGuard =
        buildPostStatement(guard, ParamPack(builder, innerLoop, endLoc, initLoc, returnLoc))
      val lastBody = body.accept(this, ParamPack(builder, lastGuard, endLoc, initLoc, returnLoc))
      xcfaEdge = XcfaEdge(lastBody, initLoc, metadata = getMetadata(statement))
      builder.addEdge(xcfaEdge)
    }
    val outerLastGuard =
      buildPostStatement(guard, ParamPack(builder, outerBeforeGuard, null, null, null))
    xcfaEdge = XcfaEdge(outerLastGuard, endLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    return endLoc
  }

  private fun buildWithoutPostStatement(cStatement: CStatement, param: ParamPack): XcfaLocation {
    Preconditions.checkState(
      cStatement is CCompound,
      "Currently only CCompounds have pre- and post statements!",
    )
    val statement = cStatement as CCompound
    val builder: XcfaProcedureBuilder = param.builder
    var lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    val preStatements = statement.preStatements
    val postStatements = statement.postStatements
    val cStatementList = statement.getcStatementList()
    val initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    val edge = XcfaEdge(lastLoc, initLoc, metadata = getMetadata(statement))
    builder.addEdge(edge)
    lastLoc = initLoc
    if (preStatements != null)
      lastLoc =
        preStatements.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
    for (i in 0 until cStatementList.size - 1) {
      val stmt = cStatementList[i]
      if (stmt != null)
        lastLoc = stmt.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
    }
    if (cStatementList.size == 0) return lastLoc
    val lastStatement = cStatementList[cStatementList.size - 1]
    lastLoc =
      if (postStatements == null) {
        buildWithoutPostStatement(
          lastStatement,
          ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc),
        )
      } else {
        lastStatement.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
      }
    return lastLoc
  }

  private fun buildPostStatement(cStatement: CStatement, param: ParamPack): XcfaLocation {
    Preconditions.checkState(
      cStatement is CCompound,
      "Currently only CCompounds have pre- and post statements!",
    )
    val statement = cStatement as CCompound
    val builder: XcfaProcedureBuilder = param.builder
    var lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    val preStatements = statement.preStatements
    val postStatements = statement.postStatements
    val cStatementList = statement.getcStatementList()
    lastLoc =
      if (postStatements != null)
        postStatements.accept(this, ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc))
      else
        buildPostStatement(
          cStatementList[cStatementList.size - 1],
          ParamPack(builder, lastLoc, breakLoc, continueLoc, returnLoc),
        )
    return lastLoc
  }

  class ParamPack(
    builder: XcfaProcedureBuilder,
    lastLoc: XcfaLocation,
    breakLoc: XcfaLocation?,
    continueLoc: XcfaLocation?,
    returnLoc: XcfaLocation?,
  ) {

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

private fun Expr<*>.hasArithmetic(): Boolean =
  when (this) {
    is AddExpr -> true
    is SubExpr -> true
    is DivExpr -> true
    is MulExpr -> true
    else -> ops.any { it.hasArithmetic() }
  }
