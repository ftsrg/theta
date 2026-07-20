/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.*
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Reference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer
import hu.bme.mit.theta.frontend.transformation.model.declaration.FunctionIds
import hu.bme.mit.theta.frontend.transformation.model.statements.*
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.BitfieldSlice
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.CPasses
import hu.bme.mit.theta.xcfa.passes.MemsafetyPass
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import java.math.BigInteger
import java.util.stream.Collectors

class FrontendXcfaBuilder(
  val parseContext: ParseContext,
  val property: XcfaProperty,
  val uniqueWarningLogger: Logger,
) : CStatementVisitorBase<FrontendXcfaBuilder.ParamPack, XcfaLocation>() {

  private val locationLut: MutableMap<String, XcfaLocation> = LinkedHashMap()
  private var ptrCnt = 1 // counts up, uses 3k+1 -- compile-time bases, for single-instance globals
    get() = field.also { field += 3 }

  private var structArgCnt = 0 // names the per-call temporaries a by-value struct argument copies into

  /**
   * If a compound statement has pre-statements, the metadata has to appear before the pre-list, but
   * evaluation of statement has to happen afterwards. i.e., statement metadata should be added only
   * once, before pre-statements and should not be re-added later when evaluated, so we collect it
   * here and filter its metadata out in/after pre-statements
   */
  val alreadyHandledStatements: MutableSet<CStatement> = LinkedHashSet()

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

  private fun getMetadata(source: CStatement): MetaData =
    CMetaData(
      lineNumberStart = source.lineNumberStart.takeIf { it != -1 },
      lineNumberStop = source.lineNumberStop.takeIf { it != -1 },
      colNumberStart = source.colNumberStart.takeIf { it != -1 },
      colNumberStop = source.colNumberStop.takeIf { it != -1 },
      offsetStart = source.offsetStart.takeIf { it != -1 },
      offsetEnd = source.offsetEnd.takeIf { it != -1 },
      sourceText = source.sourceText,
      astNodes = listOf(source),
      functionName = source.functionName.takeIf { it != "" },
      notStatementStart = alreadyHandledStatements.contains(source),
    )

  fun buildXcfa(cProgram: CProgram): XcfaBuilder {
    val builder = XcfaBuilder(cProgram.id ?: "")
    val initStmtList: MutableList<XcfaLabel> = ArrayList()
    if (MemsafetyPass.enabled) {
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
      if (
        globalDeclaration.get1().initExpr != null &&
          globalDeclaration.get1().arrayDimensions.size > 1
      ) {
        error("Not handling init expression of high dimsension array ${globalDeclaration.get1()}")
      }
      initializeGlobalVariable(
        builder,
        globalDeclaration.get2().ref,
        initStmtList,
        globalDeclaration.get1().initExpr,
        // The *variable* is atomic when its own type is -- its outermost level. `int * _Atomic p`
        // is an atomic variable; `_Atomic int *p` is a plain variable that happens to point at
        // atomic memory, and it is the memory, not `p`, that then cannot be raced on.
        globalDeclaration.get1().actualType.isAtomic,
      )
    }
    // A function whose address is taken gets a variable holding its id, so that assigning it to a
    // function pointer (`fp = f`) stores the id that FunctionPointerCallsPass dispatches on. This
    // is
    // only needed when the program actually calls through a function pointer -- taking a function's
    // address merely to pass it to pthread_create resolves it by name -- so programs without
    // indirect calls are left completely unchanged.
    for (function in if (FunctionIds.hasIndirectCall()) cProgram.functions else listOf()) {
      val id = FunctionIds.getId(function.funcDecl.name) ?: continue
      for (varDecl in function.funcDecl.varDecls) {
        val idLit = functionIdLiteral(id, varDecl.type)
        builder.addVar(XcfaGlobalVar(varDecl, idLit))
        initStmtList.add(
          AssignStmtLabel(cast(varDecl, varDecl.type), cast(idLit, varDecl.type), varDecl.type)
        )
      }
    }
    for (function in cProgram.functions) {
      val toAdd: XcfaProcedureBuilder = handleFunction(function, initStmtList, builder)
      if (toAdd.name.equals("main")) builder.addEntryPoint(toAdd, listOf())
    }
    return builder
  }

  /**
   * The function's id, as a literal of the variable that holds it.
   *
   * It cannot be built from the variable's *C* type: that is the function's return type, and a
   * `void` function's has no value representation at all. Nor can it just be built as an `int` --
   * that only coincides with the variable's type under integer arithmetic and ILP32. A function
   * returning a `long` gets a 64-bit variable, and a 32-bit literal is then a type error.
   */
  private fun functionIdLiteral(id: Int, type: Type): LitExpr<*> {
    val value = BigInteger.valueOf(id.toLong())
    return when (type) {
      is IntType -> IntExprs.Int(value)
      is BvType ->
        if (type.signed == true) BvUtils.bigIntegerToSignedBvLitExpr(value, type.size)
        else BvUtils.bigIntegerToUnsignedBvLitExpr(value, type.size)
      else -> error("Cannot represent a function id in a variable of type $type")
    }
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
      XcfaProcedureBuilder(funcDecl.name, CPasses(property, parseContext, uniqueWarningLogger))
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
        allocateStackStruct(flatVariable.ref, type, initStmtList)
      }
    }
    builder.createInitLoc(getMetadata(function))
    var init = builder.initLoc

    // (A multi-dimensional array used to be rejected here. Its rows are now allocated above, the
    // same way a struct's aggregate fields are, so `a[i][j]` reads `arrays[arrays[a][i]][j]`.)

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

  /**
   * Records a *global* struct object's size and gives every struct-typed field of it storage of its
   * own, at a compile-time base. A global is a single object -- there is only ever one activation of
   * it -- so a constant base cannot alias anything, and it stays cheaper than an allocation.
   * Stack objects need a base per activation and go through [allocateStackStruct] instead.
   *
   * A struct variable's value IS its base id, and `s.f` reads `__arrays_T[s][i]`. A field that is
   * itself a struct holds a base id in turn -- `o.in.x` is `__arrays[__arrays[o][0]][0]` -- but only
   * *declared* variables were ever given one, so `o.in`'s base stayed unconstrained and the solver
   * could pick any value it liked for it, including one already in use. `struct Out o, p; o.in.x =
   * 1; p.in.x = 2;` then read `o.in.x` back as 2: the inner structs of two distinct objects aliased.
   * That is unsound in both directions -- a write through one object shows up in an unrelated one (a
   * false alarm), and two objects the program keeps apart can be conflated (hiding a real bug).
   *
   * C has no struct that contains itself by value -- a recursive type has to go through a pointer,
   * which is a scalar field here -- so the recursion terminates.
   *
   * Unions are left as they are: their members all start at offset 0, so walking them by member
   * index does not describe their layout, and [CStruct.isUnion] accesses that would need a faithful
   * one are already refused.
   */
  private fun giveStructObjectStorage(
    builder: XcfaBuilder,
    objectExpr: Expr<*>,
    type: CStruct,
    initStmtList: MutableList<XcfaLabel>,
  ) {
    if (MemsafetyPass.enabled) {
      val fitsall = Fitsall(null, parseContext)
      initStmtList.add(
        builder.allocate(parseContext, objectExpr, fitsall.getValue("${type.unitCount}"))
      )
    }
    if (type.isUnion) return
    type.fields.forEach { field ->
      val fieldType = field.get2()
      if (fieldType is CStruct) {
        val deref =
          Dereference(
            cast(objectExpr, objectExpr.type),
            cast(type.getValue("${type.unitOffsetOf(field.get1())}"), objectExpr.type),
            fieldType.smtType,
          )
        parseContext.metadata.create(deref, "cType", fieldType)
        initStmtList.add(
          StmtLabel(
            MemoryAssignStmt.create(deref, cast(fieldType.getValue("$ptrCnt"), deref.type))
          )
        )
        giveStructObjectStorage(builder, deref, fieldType, initStmtList)
      }
    }
  }

  /**
   * Emits the `alloca(target, size)` marker [AllocaFunctionPass] lowers into a fresh runtime base.
   *
   * The size is the object's field/element count, recorded (under memsafety) so out-of-bounds
   * accesses are caught; without memsafety it is ignored and only the fresh base is assigned. The
   * target may be a variable or a memory cell -- the pass dispatches on which.
   */
  private fun alloca(target: Expr<*>, size: Int): XcfaLabel =
    InvokeLabel(
      "alloca",
      listOf(target, Fitsall(null, parseContext).getValue("$size")),
      metadata = EmptyMetaData,
    )

  /**
   * Gives a *stack-allocated* struct a fresh runtime base -- for the object and, recursively, for
   * every struct-typed field -- from the allocation counter, instead of a compile-time constant.
   *
   * A struct's value is its base id. When that base was a constant baked into the procedure's init,
   * every activation of the procedure reused it: two recursive frames, or two threads running the
   * function, shared one `arrays[base]`, so a write in one was seen by the other and a race-free
   * program came back a false alarm (`mt_struct`: a thread-local struct, reported Unsafe). A base
   * drawn from the runtime counter ([alloca]) is distinct per activation, which is what C guarantees.
   *
   * A struct-typed field is a subobject whose base lives in the cell `arrays[parent][i]`, so it is
   * allocated in turn into that cell (the pass writes the fresh base there). C has no by-value
   * self-containing struct, so this terminates. Unions keep the single object their offset-0 model
   * needs, exactly as [giveStructObjectStorage] leaves them for globals.
   *
   * Globals stay on the compile-time path ([giveStructObjectStorage]): a global is a single object,
   * so a constant base cannot alias anything.
   */
  private fun allocateStackStruct(target: Expr<*>, type: CStruct, labels: MutableList<XcfaLabel>) {
    labels.add(alloca(target, type.unitCount))
    if (type.isUnion) return
    type.fields.forEach { field ->
      allocateStackSubobject(
        subobjectCell(target, type, type.unitOffsetOf(field.get1()), field.get2()),
        field.get2(),
        labels,
      )
    }
  }

  /**
   * Gives a *stack-allocated* array a fresh runtime base, and -- if its elements are themselves
   * aggregates -- allocates each of them in turn.
   *
   * An array of scalars is one block: the elements live directly in it (`arrays[a][k]`), so nothing
   * more is allocated. An array of structs (or of arrays) holds a base per element in those cells,
   * exactly like a struct holds one per field, so each element is allocated into its cell. A member
   * array has a constant bound, so the element count is known; a flexible array member (no bound) is
   * left unallocated, the pre-existing limitation for a member whose size the declaration omits.
   */
  private fun allocateStackArray(target: Expr<*>, type: CArray, labels: MutableList<XcfaLabel>) {
    // Sized by the whole object: a multi-dimensional array's dimensions multiply, since its rows
    // live in the same block rather than in objects of their own.
    val size = flatArraySize(type) ?: return
    labels.add(alloca(target, size))
    allocateArrayElements(target, type, labels)
  }

  /**
   * Gives each element of [target] an object of its own, when the elements are themselves
   * aggregates -- a row of `int a[3][4]`, or an element of `struct S a[3]`. Such an array holds a
   * base per element in its cells, exactly as a struct holds one per field; leaving those bases
   * unconstrained lets the solver conflate two elements, so `a[1][2] = 7` could be read back
   * through `a[0][0]`. An array of scalars keeps its elements directly in its own cells and needs
   * nothing here.
   *
   * Split out from [allocateStackArray] because a *declared* local array already gets its own base
   * from the `alloca` the frontend emits at the declaration; only its elements are missing, and
   * they have to be allocated after that base is assigned, not before.
   */
  /** How many array elements are worth giving an object of their own; see below. */
  private val MAX_ELEMENT_ALLOCATIONS = 1024

  private fun allocateArrayElements(
    target: Expr<*>,
    type: CArray,
    labels: MutableList<XcfaLabel>,
  ) {
    val size = fixedArraySize(type) ?: return
    val elementType = type.embeddedType
    // An array of arrays is one contiguous object -- `int a[3][4]` is twelve cells, addressed as
    // arrays[a][i*4 + j] -- so its rows are not objects and nothing is allocated for them. Only an
    // element that is a *struct* is an object in its own right (a struct's value is its base id).
    if (elementType !is CStruct) return
    if (size > MAX_ELEMENT_ALLOCATIONS) {
      // One allocation per element does not scale: the benchmarks contain `S a[1000000]`, and
      // emitting a million of them makes the frontend run out of time long before the analysis
      // starts. Above the cap the elements keep sharing an unconstrained base, as they did before
      // any of them were allocated -- imprecise for such an array, but bounded. Giving every
      // element a base without naming it one statement at a time needs the derived-base memory
      // model (AD7), which is the real fix.
      return
    }
    for (index in 0 until size) {
      allocateStackSubobject(subobjectCell(target, type, index, elementType), elementType, labels)
    }
  }

  private fun allocateStackSubobject(
    cell: Expr<*>,
    type: CComplexType,
    labels: MutableList<XcfaLabel>,
  ) {
    when (type) {
      is CStruct -> allocateStackStruct(cell, type, labels)
      is CArray -> allocateStackArray(cell, type, labels)
      else -> {} // a scalar field lives in its parent's cell; it needs no object of its own
    }
  }

  /** The cell `arrays[parent][index]` a subobject (struct field, array element) lives at. */
  private fun subobjectCell(
    parent: Expr<*>,
    parentType: CComplexType,
    index: Int,
    subobjectType: CComplexType,
  ): Dereference<*, *, *> =
    Dereference(
        cast(parent, parent.type),
        cast(parentType.getValue("$index"), parent.type),
        subobjectType.smtType,
      )
      .also { parseContext.metadata.create(it, "cType", subobjectType) }

  /**
   * An array's constant element count, or null when there isn't one: a flexible array member (no
   * bound at all) or a variable-length array, whose length is only known at run time. Callers use
   * it to decide how many subobjects to allocate, so "no constant count" has to be an answer
   * rather than an error -- a VLA simply gets no per-element allocation.
   */
  private fun fixedArraySize(type: CArray): Int? {
    val dimension = type.arrayDimension ?: return null
    return when (val bounds = ExprUtils.simplify(dimension.expression)) {
      is IntLitExpr -> bounds.value.toInt()
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(bounds).toInt()
      else -> null
    }
  }

  /**
   * The number of cells an array occupies. A multi-dimensional array is contiguous -- `int a[3][4]`
   * is twelve cells addressed as `arrays[a][i*4 + j]` -- so the dimensions multiply. Null when any
   * of them is not a compile-time constant.
   */
  private fun flatArraySize(type: CArray): Int? {
    val size = fixedArraySize(type) ?: return null
    val elementType = type.embeddedType
    if (elementType !is CArray) return size
    val inner = flatArraySize(elementType) ?: return null
    return size * inner
  }

  /**
   * Whether assigning [rExpression] to a variable of this type is a struct copy.
   *
   * The right-hand side has to be a struct of the same type: an expression whose recorded C type was
   * lost reads back as the plain integer its base id is stored as, and is left to the ordinary
   * assignment below rather than walked as if it had fields.
   *
   * Unions are excluded, and go on assigning the base as before. Their members all start at offset 0
   * rather than at successive indices, so copying them member by member does not describe their
   * layout -- the same reason [giveStructObjectStorage] does not walk into them.
   */
  private fun CComplexType.isCopiedStruct(rExpression: Expr<*>): Boolean =
    this is CStruct && !this.isUnion && this == CComplexType.getType(rExpression, parseContext)

  /**
   * Copies a struct object's contents into another, field by field.
   *
   * A struct variable's value is a base id, so `b = a` assigned *a's base* to `b` -- after which the
   * two names denoted one object, and a later write to `a` was read back through `b`. C copies here,
   * so `b` has to keep its own storage and receive a's values:
   * ```c
   * struct T a, b; a.len = 1; b = a; a.len = 2;   /* b.len is still 1 */
   * ```
   * The copy is deep. A field that is itself a struct or an array is a subobject, not a reference to
   * one, so its *contents* are copied and the destination keeps the base it was allocated
   * ([allocateStackStruct], or [giveStructObjectStorage] for a global); copying the base instead
   * would alias the two objects and reintroduce the same bug one level down. An array is copied
   * element by element for the same reason.
   *
   * A flexible array member (no bound) has no element count to copy over, so it falls back to a base
   * assignment -- the pre-existing limitation for a member whose size the declaration omits.
   */
  private fun structCopy(
    target: Expr<*>,
    source: Expr<*>,
    type: CStruct,
    metadata: MetaData,
  ): List<XcfaLabel> =
    // Bitfields sharing a storage unit map to the same cell, so the copy of that cell is simply
    // repeated -- idempotent, and it carries all the packed fields at once.
    type.fields.flatMap { field ->
      val fieldType = field.get2()
      val unit = type.unitOffsetOf(field.get1())
      copySubobject(
        subobjectCell(target, type, unit, fieldType),
        subobjectCell(source, type, unit, fieldType),
        fieldType,
        metadata,
      )
    }

  /** Copies an array object's elements into another, element by element. */
  private fun arrayCopy(
    target: Expr<*>,
    source: Expr<*>,
    type: CArray,
    metadata: MetaData,
  ): List<XcfaLabel> {
    val size = fixedArraySize(type) ?: return copyScalar(target, source, metadata)
    val elementType = type.embeddedType
    return (0 until size).flatMap { index ->
      copySubobject(
        subobjectCell(target, type, index, elementType),
        subobjectCell(source, type, index, elementType),
        elementType,
        metadata,
      )
    }
  }

  private fun copySubobject(
    to: Expr<*>,
    from: Expr<*>,
    type: CComplexType,
    metadata: MetaData,
  ): List<XcfaLabel> =
    when {
      type is CStruct && !type.isUnion -> structCopy(to, from, type, metadata)
      type is CArray -> arrayCopy(to, from, type, metadata)
      else -> copyScalar(to, from, metadata)
    }

  private fun copyScalar(to: Expr<*>, from: Expr<*>, metadata: MetaData): List<XcfaLabel> =
    listOf(
      StmtLabel(
        MemoryAssignStmt.create(to as Dereference<*, *, *>, cast(from, to.type)),
        metadata = metadata,
      )
    )

  /**
   * Passes a struct argument *by value*: copies it into a fresh object and hands the callee that.
   *
   * A struct's value is its base id, so passing the variable passed *the caller's object* -- the
   * callee's parameter took the same base, and a write to a by-value parameter was read back by the
   * caller (`void f(struct T t){ t.len = 9; }` mutated the argument). C copies at the call, so the
   * argument is copied into a new object here and the callee is given that object's base instead.
   *
   * The object is a stack allocation like any other local ([allocateStackStruct]), held by a
   * per-call temporary: its base comes from the runtime counter, so two threads calling the function
   * at once copy into distinct objects rather than a shared constant one. The copy is deep. The
   * parameter is pure IN -- a by-value struct is never copied back out -- so the temporary is only
   * ever written here and read by the callee's binding.
   *
   * Returns the temporary's ref to pass and the labels that allocate and fill it, to run before the
   * call.
   */
  private fun copyStructArgument(
    builder: XcfaProcedureBuilder,
    argExpr: Expr<*>,
    type: CStruct,
    metadata: MetaData,
  ): Pair<Expr<*>, List<XcfaLabel>> {
    val tmp = Var("__theta_structarg" + structArgCnt++, type.smtType)
    parseContext.metadata.create(tmp.ref, "cType", type)
    builder.addVar(tmp)
    val labels: MutableList<XcfaLabel> = ArrayList()
    allocateStackStruct(tmp.ref, type, labels)
    labels.addAll(structCopy(tmp.ref, argExpr, type, metadata))
    return tmp.ref to labels
  }

  private fun initializeGlobalVariable(
    builder: XcfaBuilder,
    globalDeclaration: Expr<*>,
    initStmtList: MutableList<XcfaLabel>,
    initExpr: CStatement? = null,
    isAtomic: Boolean = false,
  ) {
    val type = CComplexType.getType(globalDeclaration, parseContext)
    if (type is CVoid) {
      return
    }
    if (globalDeclaration is RefExpr<*>) {
      builder.addVar(
        XcfaGlobalVar(globalDeclaration.decl as VarDecl<*>, type.nullValue, atomic = isAtomic)
      )
    }
    if (type is CArray) {
      initStmtList.add(AssignStmtLabel(globalDeclaration, type.getValue("$ptrCnt")))
      if (MemsafetyPass.enabled) {
        // Sized or initializer-sized, the count comes from getArraySize; re-materializing the
        // literal through getValue types it for the *current* arithmetic. The stored dimension
        // expression cannot be used directly: types registered by the early typedef pass carry
        // dimension literals typed for the default arithmetic, not the decided one.
        val bounds =
          CComplexType.getUnsignedLong(parseContext)
            .getValue(getArraySize(type, initExpr).toString())
        initStmtList.add(builder.allocate(parseContext, globalDeclaration, bounds))
      }
      initializeCompound(
        builder,
        getArraySize(type, initExpr),
        { type.embeddedType },
        initExpr,
        initStmtList,
        globalDeclaration,
      )
    } else if (type is CStruct) {
      initStmtList.add(AssignStmtLabel(globalDeclaration, type.getValue("$ptrCnt")))
      giveStructObjectStorage(builder, globalDeclaration, type, initStmtList)
      // An initializer list is what initializeCompound is for; asking it for a single
      // `.expression` throws. Anything else that has one is genuinely unsupported here.
      if (
        initExpr != null &&
          initExpr !is CInitializerList &&
          initExpr.expression !is UnsupportedInitializer
      ) {
        error("Unsupported initializer for global struct variable $globalDeclaration.")
      }
      // Storage is per unit, not per member: packed bitfields share a cell. For a bitfield-free
      // struct every member is its own unit, so this is the historical field-indexed iteration.
      val unitTypes =
        (0 until type.unitCount).map { unit ->
          type.fields.first { type.unitOffsetOf(it.get1()) == unit }.get2()
        }
      if (type.unitCount != type.fields.size && initExpr is CInitializerList) {
        // A brace initializer names members, which no longer map one-to-one onto cells.
        initializePackedStruct(
          builder,
          type,
          { unitTypes[it] },
          initExpr,
          initStmtList,
          globalDeclaration,
        )
      } else {
        initializeCompound(
          builder,
          type.unitCount,
          { unitTypes[it] },
          initExpr,
          initStmtList,
          globalDeclaration,
        )
      }
    } else {
      if (initExpr != null && initExpr.expression !is UnsupportedInitializer) {
        initStmtList.add(AssignStmtLabel(globalDeclaration, type.castTo(initExpr.expression)))
      } else {
        initStmtList.add(AssignStmtLabel(globalDeclaration, type.nullValue))
      }
    }
  }

  private fun initializeCompound(
    builder: XcfaBuilder,
    dimension: Int,
    embeddedType: (Int) -> CComplexType,
    initExpr: CStatement?,
    initStmtList: MutableList<XcfaLabel>,
    globalDeclaration: Expr<*>,
  ) {
    val initExprs = elementPositions(initExpr)
    for (i in 0 until dimension) {
      val et = embeddedType(i)
      val embeddedDeclaration =
        Dereference(globalDeclaration, offsetLiteral(i.toLong()), et.smtType)
      parseContext.metadata.create(embeddedDeclaration, "cType", et)
      initializeGlobalVariable(builder, embeddedDeclaration, initStmtList, initExprs[i])
    }
  }

  /**
   * The initializer elements by the position they write: a designator sets the position, anything
   * else takes the next one. For a struct the position is a *field* index (see
   * `DeclarationVisitor#designatedPosition`), which stops being the storage cell once bitfields
   * pack.
   */
  private fun elementPositions(initExpr: CStatement?): Map<Int, CStatement> =
    (initExpr as? CInitializerList)
      ?.statements
      ?.mapIndexed { i, it -> Pair(designatedIndex(it.get1()) ?: i, it.get2()) }
      ?.toMap() ?: emptyMap()

  /** A member offset as a literal of the current arithmetic's pointer-sized type. */
  private fun offsetLiteral(x: Long): Expr<*> =
    if (CComplexType.getUnsignedLong(parseContext).smtType is IntType)
      IntLitExpr.of(BigInteger.valueOf(x))
    else
      BvUtils.bigIntegerToNeutralBvLitExpr(
        BigInteger.valueOf(x),
        (CComplexType.getUnsignedLong(parseContext).smtType as BvType).size,
      )

  /**
   * Initialize a struct whose bitfields pack into shared storage units.
   *
   * A brace initializer names members, but storage is per unit, so several elements can land in one
   * cell: `struct { unsigned a:4, b:4; } s = {1, 2}` is one cell holding `0x21`, not two cells. Each
   * unit's value is folded from its members' initializers at their bit offsets -- the same splice as
   * an assignment to a bitfield ([BitfieldSlice.write]) -- and the cell is assigned once. Members
   * the initializer omits keep the zero they fold onto, which is what C guarantees them.
   *
   * A unit holding a single ordinary member keeps the recursive path, so a nested struct or array
   * member still initializes element-wise rather than being squeezed into an integer.
   */
  private fun initializePackedStruct(
    builder: XcfaBuilder,
    type: CStruct,
    unitType: (Int) -> CComplexType,
    initExpr: CInitializerList,
    initStmtList: MutableList<XcfaLabel>,
    globalDeclaration: Expr<*>,
  ) {
    val initExprs = elementPositions(initExpr)
    val slotOf = { field: Int -> type.slotOf(type.fields[field].get1())!! }
    for (unit in 0 until type.unitCount) {
      val cellType = unitType(unit)
      val cell = Dereference(globalDeclaration, offsetLiteral(unit.toLong()), cellType.smtType)
      parseContext.metadata.create(cell, "cType", cellType)
      val members = type.fields.indices.filter { slotOf(it).unitIndex() == unit }
      if (members.size == 1 && !slotOf(members[0]).bitfield()) {
        initializeGlobalVariable(builder, cell, initStmtList, initExprs[members[0]])
        continue
      }
      // Fold onto zero rather than onto a read of the cell: the object was just created, and none
      // of its cells is assigned before this point.
      var value: Expr<*> = cellType.nullValue
      for (field in members) {
        val element = initExprs[field] ?: continue
        val slot = slotOf(field)
        value =
          BitfieldSlice.write(
            value,
            cellType.castTo(element.expression),
            slot.bitOffset(),
            slot.width(),
          )
      }
      initStmtList.add(AssignStmtLabel(cell, cellType.castTo(value)))
    }
  }

  /** The position a designated element writes, or null for take-the-next-slot. */
  private fun designatedIndex(designator: java.util.Optional<CStatement>): Int? =
    designator.map { (it.expression as IntLitExpr).value.toInt() }.orElse(null)

  private fun getArraySize(type: CArray, initExpr: CStatement?): Int {
    if (type.arrayDimension == null) {
      if (initExpr is CInitializerList) {
        // `[9] = x` extends the array: the size is the highest written position + 1.
        return initExpr.statements
          .mapIndexed { i, it -> designatedIndex(it.get1()) ?: i }
          .maxOrNull()
          ?.plus(1) ?: 0
      } else {
        throw UnsupportedFrontendElementException(
          "Array with unspecified size must have initializer list."
        )
      }
    }
    // No castTo here: only the literal's value is needed, and the dimension expression may be
    // typed for the wrong arithmetic (types registered by the early typedef pass carry
    // default-arithmetic literals; casting one with the bitvector visitor throws).
    val bounds = ExprUtils.simplify(type.arrayDimension.expression)
    checkState(
      bounds is IntLitExpr || bounds is BvLitExpr,
      "Only IntLit and BvLit expression expected here.",
    )
    val literalValue =
      if (bounds is IntLitExpr) bounds.value.toInt()
      else BvUtils.neutralBvLitExprToBigInteger(bounds as BvLitExpr).toInt()
    return literalValue
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
    var xcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = EmptyMetaData)
    builder.addEdge(xcfaEdge)
    val location = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(location)
    initLoc = rValue.accept(this, ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc))
    val rExpression = statement.getrExpression()
    // Assigning to a packed bitfield writes only its own bits: read the shared cell, splice the
    // new value in, and store the cell back. Without this the neighbouring fields in the same
    // storage unit would be clobbered.
    val bitfieldCell =
      parseContext.metadata.getMetadataValue(lValue, BitfieldSlice.CELL).orElse(null)
        as? Dereference<*, *, *>
    val label: XcfaLabel =
      if (bitfieldCell != null) {
        val bitOffset =
          (parseContext.metadata.getMetadataValue(lValue, BitfieldSlice.OFFSET).orElseThrow()
            as Number)
            .toInt()
        val fieldWidth =
          (parseContext.metadata.getMetadataValue(lValue, BitfieldSlice.WIDTH).orElseThrow()
            as Number)
            .toInt()
        val cellType = CComplexType.getType(bitfieldCell, parseContext)
        val newCell =
          BitfieldSlice.write(bitfieldCell, cellType.castTo(rExpression), bitOffset, fieldWidth)
        val op = cast(bitfieldCell.array, bitfieldCell.array.type)
        val offset = cast(bitfieldCell.offset, op.type)
        val deref = Dereference(op, offset, cellType.smtType)
        parseContext.metadata.create(deref, "cType", CPointer(null, cellType, parseContext))
        StmtLabel(
          MemoryAssignStmt.create(deref, cast(newCell, deref.type)),
          metadata = getMetadata(statement),
        )
      } else
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
          val lhsType = CComplexType.getType(lValue, parseContext)
          if (
            (lhsType is CPointer || lhsType is CArray || lhsType is CStruct) &&
              rExpression.hasArithmetic()
          ) {
            // A pointer *value* is an object id: memory is `arrays[base][offset]`, so the offset
            // has nowhere to live in the pointer itself. `p = q + i` is therefore rewritten to
            // `p = &q[i]` (`ref(deref(q, i))`): ReferenceElimination splits `p` into `p_base` /
            // `p_offset` and gives the offset a home, exactly as `*(q + i)` keeps the index at the
            // dereference. This is how CIL spells array and field access (`tmp = base + idx;
            // *tmp`).
            // Only a `pointer + integer(s)` shape is handled; anything else -- a pointer
            // difference,
            // or a pointer buried under a multiply -- is still refused rather than answered
            // wrongly.
            val asReference =
              rExpression.asPointerArithReference(lhsType, parseContext)
                ?: throw UnsupportedFrontendElementException(
                  "Pointer arithmetic not supported: $lValue = $rExpression"
                )
            AssignStmtLabel(
              lValue,
              cast(asReference, lValue.type),
              metadata = getMetadata(statement),
            )
          } else if (lhsType.isCopiedStruct(rExpression)) {
            SequenceLabel(
              structCopy(lValue, rExpression, lhsType as CStruct, getMetadata(statement)),
              metadata = getMetadata(statement),
            )
          } else {
            // TODO: check if assignment to arrays (stack AND heap) are value- or pointer-based
            AssignStmtLabel(
              lValue,
              cast(lhsType.castTo(rExpression), lValue.type),
              metadata = getMetadata(statement),
            )
          }
        }

        else -> {
          error("Could not handle left-hand side of assignment $statement")
        }
      }

    // Giving a local array its base is the moment its elements can be allocated: a declared array
    // gets that base from the `alloca` the frontend emits at its declaration, and an array is not
    // otherwise assignable in C, so this fires exactly once per array. Elements that are
    // aggregates need objects of their own -- see [allocateArrayElements].
    val lhsType = CComplexType.getType(lValue, parseContext)
    val elementLabels = mutableListOf<XcfaLabel>()
    if (lValue is RefExpr<*> && lhsType is CArray) {
      allocateArrayElements(lValue, lhsType, elementLabels)
    }
    val edgeLabel =
      if (elementLabels.isEmpty()) label
      else SequenceLabel(listOf(label) + elementLabels, metadata = getMetadata(statement))

    xcfaEdge = XcfaEdge(initLoc, location, edgeLabel, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
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
    var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = EmptyMetaData)
    builder.addEdge(xcfaEdge)
    val location = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(location)
    xcfaEdge =
      XcfaEdge(
        initLoc,
        location,
        StmtLabel(
          statement.assumeStmt,
          choiceType = ChoiceType.NONE,
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
    var edge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = EmptyMetaData)
    builder.addEdge(edge)
    check(breakLoc != null)
    edge = XcfaEdge(initLoc, breakLoc, metadata = EmptyMetaData)
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
    var initLoc = getLoc(builder, statement.id, EmptyMetaData)
    builder.addLoc(initLoc)
    var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = EmptyMetaData)
    builder.addEdge(xcfaEdge)
    val location = getAnonymousLoc(builder, metadata = EmptyMetaData)
    builder.addLoc(location)
    val params: MutableList<Expr<*>> = ArrayList()
    builder.addVar(ret)
    params.add(ret.ref)
    for (cStatement in myParams) {
      initLoc =
        cStatement.accept(this, ParamPack(builder, initLoc, breakLoc, continueLoc, returnLoc))
    }
    val prepLabels: MutableList<XcfaLabel> = ArrayList()
    for (cStatement in myParams) {
      val argExpr = cStatement.expression
      val argType = CComplexType.getType(argExpr, parseContext)
      if (argType is CStruct && !argType.isUnion) {
        val (byValue, prep) =
          copyStructArgument(builder, argExpr, argType, getMetadata(statement))
        prepLabels.addAll(prep)
        params.add(byValue)
      } else {
        params.add(argExpr)
      }
    }
    val call = InvokeLabel(statement.functionId, params, metadata = getMetadata(statement))
    val label =
      if (prepLabels.isEmpty()) call
      else SequenceLabel(prepLabels + call, metadata = getMetadata(statement))
    xcfaEdge = XcfaEdge(initLoc, location, label, metadata = getMetadata(statement))
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
    val initLoc = getLoc(builder, statement.id, metadata = EmptyMetaData)
    builder.addLoc(initLoc)
    val (edge, innerStmt) =
      if (
        statement.getcStatementList().size == 1 &&
          (statement.preStatements as? CCompound)?.getcStatementList()?.isNotEmpty() == true
      ) {
        val metadata = getMetadata(statement.getcStatementList()[0])
        Pair(
          XcfaEdge(
            lastLoc,
            initLoc,
            StmtLabel(SkipStmt.getInstance(), metadata = metadata),
            metadata = metadata,
          ),
          statement.getcStatementList()[0],
        )
      } else {
        Pair(XcfaEdge(lastLoc, initLoc, metadata = EmptyMetaData), null)
      }
    if (innerStmt != null) alreadyHandledStatements.add(innerStmt)
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
    if (innerStmt != null) alreadyHandledStatements.remove(innerStmt)
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
    var edge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = EmptyMetaData)
    builder.addEdge(edge)
    check(continueLoc != null)
    edge = XcfaEdge(initLoc, continueLoc, metadata = EmptyMetaData)
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
    var xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = EmptyMetaData)
    builder.addEdge(xcfaEdge)
    val lastBody = body.accept(this, ParamPack(builder, initLoc, endLoc, innerEndLoc, returnLoc))
    xcfaEdge = XcfaEdge(lastBody, innerEndLoc, metadata = getMetadata(statement))
    builder.addEdge(xcfaEdge)
    val lastPre =
      buildWithoutPostStatement(guard, ParamPack(builder, innerEndLoc, null, null, returnLoc))
    // The guard test is re-evaluated on every loop cycle, whereas the `do` statement itself is
    // entered only once. The waypoint location comes from the label's metadata (see
    // TraceToWitness),
    // so the label must carry the body's metadata -- not the whole do-while statement's -- to keep
    // a
    // cycled witness waypoint off the `do` keyword (matching CWhile/CFor).
    val assume =
      StmtLabel(
        Stmts.Assume(
          AbstractExprs.Neq(
            guard.expression,
            CComplexType.getType(guard.expression, parseContext).nullValue,
          )
        ),
        choiceType = ChoiceType.MAIN_PATH,
        metadata = getMetadata(body),
      )
    xcfaEdge = XcfaEdge(lastPre, innerInnerGuard, assume, metadata = getMetadata(body))
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
        metadata = EmptyMetaData,
      )
    xcfaEdge = XcfaEdge(lastPre, outerInnerGuard, assume1, metadata = getMetadata(body))
    builder.addEdge(xcfaEdge)
    val outerLastGuard =
      buildPostStatement(guard, ParamPack(builder, outerInnerGuard, null, null, null))
    val innerLastGuard =
      buildPostStatement(guard, ParamPack(builder, innerInnerGuard, null, null, null))
    xcfaEdge = XcfaEdge(outerLastGuard, endLoc, metadata = EmptyMetaData)
    builder.addEdge(xcfaEdge)
    xcfaEdge = XcfaEdge(innerLastGuard, initLoc, metadata = EmptyMetaData)
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
    // The guard-branch edges below are re-traversed on every loop cycle, whereas the `for`
    // statement itself is entered only once. Anchoring them to the body's metadata (as CWhile does)
    // makes a cycled witness waypoint point at the loop body rather than the `for` keyword.
    val bodyMetadata = if (body == null) getMetadata(statement) else getMetadata(body)
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
        metadata = bodyMetadata,
      )
    check(lastTest != null)
    xcfaEdge = XcfaEdge(lastTest, endInit, assume, metadata = bodyMetadata)
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
        metadata = EmptyMetaData,
      )
    xcfaEdge = XcfaEdge(lastTest, outerLastTest, assume1, metadata = bodyMetadata)
    builder.addEdge(xcfaEdge)
    val innerLastGuard =
      if (guard == null) endInit
      else buildPostStatement(guard, ParamPack(builder, endInit, endLoc, startIncrement, returnLoc))
    val lastBody =
      if (body == null) innerLastGuard
      else body.accept(this, ParamPack(builder, innerLastGuard, endLoc, startIncrement, returnLoc))
    xcfaEdge = XcfaEdge(lastBody, startIncrement, metadata = EmptyMetaData)
    builder.addEdge(xcfaEdge)
    if (increment != null) {
      val lastIncrement =
        increment.accept(this, ParamPack(builder, startIncrement, null, null, returnLoc))
      xcfaEdge = XcfaEdge(lastIncrement, lastInit, metadata = EmptyMetaData)
      builder.addEdge(xcfaEdge)
    } else {
      xcfaEdge = XcfaEdge(startIncrement, lastInit, metadata = EmptyMetaData)
      builder.addEdge(xcfaEdge)
    }
    val outerLastGuard =
      if (guard == null) outerLastTest
      else
        buildPostStatement(
          guard,
          ParamPack(builder, outerLastTest, endLoc, startIncrement, returnLoc),
        )
    xcfaEdge = XcfaEdge(outerLastGuard, endLoc, metadata = EmptyMetaData)
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
        metadata = getMetadata(statement),
      )
    xcfaEdge = XcfaEdge(endGuard, mainBranch, assume, metadata = getMetadata(body))
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
    xcfaEdge = XcfaEdge(endGuard, elseBranch, assume1, metadata = getMetadata(body))
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
      xcfaEdge = XcfaEdge(elseEnd, endLoc, metadata = EmptyMetaData)
      builder.addEdge(xcfaEdge)
    } else {
      val elseAfterGuard =
        buildPostStatement(guard, ParamPack(builder, elseBranch, breakLoc, continueLoc, returnLoc))
      xcfaEdge = XcfaEdge(elseAfterGuard, endLoc, metadata = EmptyMetaData)
      builder.addEdge(xcfaEdge)
    }
    xcfaEdge = XcfaEdge(mainEnd, endLoc, metadata = EmptyMetaData)
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
    val xcfaEdge: XcfaEdge = XcfaEdge(lastLoc, initLoc, metadata = EmptyMetaData)
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

  /**
   * `switch (v) case k:` compares the controlling value against each label. C converts the labels
   * to the (promoted) type of the controlling expression, so the two operands may differ in width
   * (`switch` on a `size_t` with `int` labels); comparing them directly asks the core to unify
   * `(Bv 64)` with `(Bv 32)` and throws. Compare in their smallest common type instead.
   */
  private fun switchTestEq(testValue: Expr<*>, caseValue: Expr<*>): Expr<BoolType> {
    val common =
      CComplexType.getSmallestCommonType(
        listOf(
          CComplexType.getType(testValue, parseContext),
          CComplexType.getType(caseValue, parseContext),
        ),
        parseContext,
      )
    return AbstractExprs.Eq(common.castTo(testValue), common.castTo(caseValue))
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
            BoolExprs.Not(switchTestEq(testValue.expression, cStatement.expr.expression)),
          )
      }
    }
    var lastLocation: XcfaLocation? = null
    for (cStatement in body.getcStatementList()) {
      val location = getAnonymousLoc(builder, metadata = getMetadata(statement))
      builder.addLoc(location)
      var xcfaEdge: XcfaEdge
      if (lastLocation != null) {
        xcfaEdge = XcfaEdge(lastLocation, location, metadata = EmptyMetaData)
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
            Stmts.Assume(switchTestEq(testValue.expression, cStatement.expr.expression)),
            choiceType = ChoiceType.MAIN_PATH,
            metadata = getMetadata(cStatement),
          )
        xcfaEdge = XcfaEdge(afterGuard, location, assume, metadata = getMetadata(cStatement))
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
        xcfaEdge = XcfaEdge(afterGuard, location, assume, metadata = getMetadata(cStatement))
        builder.addEdge(xcfaEdge)
      }
      lastLocation =
        cStatement.accept(this, ParamPack(builder, location, endLoc, continueLoc, returnLoc))
    }
    if (lastLocation != null) {
      val xcfaEdge: XcfaEdge = XcfaEdge(lastLocation, endLoc, metadata = EmptyMetaData)
      builder.addEdge(xcfaEdge)
    }
    return endLoc
  }

  override fun visit(statement: CWhile, param: ParamPack): XcfaLocation {
    val builder: XcfaProcedureBuilder = param.builder
    val lastLoc = param.lastLoc
    val breakLoc = param.breakLoc
    val continueLoc = param.continueLoc
    val returnLoc = param.returnLoc
    val guard = statement.guard
    val body = statement.body
    var initLoc = getLoc(builder, statement.id, metadata = getMetadata(statement))
    builder.addLoc(initLoc)
    var xcfaEdge: XcfaEdge =
      XcfaEdge(
        lastLoc,
        initLoc,
        label = StmtLabel(SkipStmt.getInstance(), metadata = getMetadata(statement)),
        metadata = getMetadata(statement),
      )
    builder.addEdge(xcfaEdge)
    val endLoc = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(endLoc)
    val outerBeforeGuard = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(outerBeforeGuard)
    val innerLoop = getAnonymousLoc(builder, metadata = getMetadata(statement))
    builder.addLoc(innerLoop)
    val testEndLoc =
      buildWithoutPostStatement(guard, ParamPack(builder, initLoc, null, null, returnLoc))
    val assume =
      StmtLabel(
        Assume(
          AbstractExprs.Neq(
            guard.expression,
            CComplexType.getType(guard.expression, parseContext).nullValue,
          )
        ),
        choiceType = ChoiceType.MAIN_PATH,
        metadata = getMetadata(body),
      )
    xcfaEdge = XcfaEdge(testEndLoc, innerLoop, assume, metadata = getMetadata(body))
    builder.addEdge(xcfaEdge)
    val assume1 =
      StmtLabel(
        Assume(
          AbstractExprs.Eq(
            guard.expression,
            CComplexType.getType(guard.expression, parseContext).nullValue,
          )
        ),
        choiceType = ChoiceType.ALTERNATIVE_PATH,
        metadata = EmptyMetaData,
      )
    xcfaEdge = XcfaEdge(testEndLoc, outerBeforeGuard, assume1, metadata = getMetadata(body))
    builder.addEdge(xcfaEdge)
    val lastGuard =
      buildPostStatement(guard, ParamPack(builder, innerLoop, endLoc, initLoc, returnLoc))
    val lastBody = body.accept(this, ParamPack(builder, lastGuard, endLoc, initLoc, returnLoc))
    xcfaEdge = XcfaEdge(lastBody, initLoc, metadata = EmptyMetaData)
    builder.addEdge(xcfaEdge)
    val outerLastGuard =
      buildPostStatement(guard, ParamPack(builder, outerBeforeGuard, null, null, null))
    xcfaEdge = XcfaEdge(outerLastGuard, endLoc, metadata = EmptyMetaData)
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

  override fun visit(statement: CNullStatement, param: ParamPack): XcfaLocation {
    return param.lastLoc
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

/** Every pointer/array-typed leaf reachable in this expression (a pointer *value*, i.e. a base). */
private fun Expr<*>.pointerLeaves(parseContext: ParseContext): List<Expr<*>> {
  if (this is RefExpr<*>) {
    when (CComplexType.getType(this, parseContext)) {
      is CPointer,
      is CArray -> return listOf(this)
      else -> {}
    }
  }
  return ops.flatMap { it.pointerLeaves(parseContext) }
}

/** This expression with every occurrence of [target] replaced by [replacement]. */
@Suppress("UNCHECKED_CAST")
private fun <T : Type> Expr<T>.replaceExpr(target: Expr<*>, replacement: Expr<*>): Expr<T> =
  if (this == target) replacement as Expr<T>
  else this.withOps(this.ops.map { (it as Expr<Type>).replaceExpr(target, replacement) }) as Expr<T>

/**
 * Reads a `pointer + integer(s)` expression as the address of an element -- `q + i` as `&q[i]`,
 * i.e. `ref(deref(q, i))` -- so it can be assigned to a pointer variable through
 * [hu.bme.mit.theta.xcfa.passes.ReferenceElimination]'s base/offset split. Subtraction arrives here
 * as `q + (-i)` (the frontend lowers `-` to `+ neg`), so it is covered too, and the arithmetic may
 * be wrapped in the bitvector casts CIL emits (`bvadd (extract q 0 32) i`).
 *
 * The pointer is the one pointer-typed leaf; the offset is the whole expression with that leaf set
 * to zero (so any surrounding casts and constants are preserved). Returns null when the shape is
 * not a single pointer plus an index -- a pointer difference, or no pointer at all -- so the caller
 * refuses it rather than answering wrongly.
 */
@Suppress("UNCHECKED_CAST")
private fun Expr<*>.asPointerArithReference(
  ptrType: CComplexType,
  parseContext: ParseContext,
): Expr<*>? {
  val leaves = pointerLeaves(parseContext)
  if (leaves.size != 1) return null
  val base = leaves[0]
  val elemType =
    when (val baseType = CComplexType.getType(base, parseContext)) {
      is CPointer -> baseType.embeddedType
      is CArray -> baseType.embeddedType
      else -> return null
    }
  // The net index: the arithmetic with the pointer contribution removed. Cast to a *signed* long so
  // subtraction (which arrives as `+ (-i)`) and the accumulated offset of chained arithmetic
  // compose
  // to the right value rather than to `2^w - i` under unbounded-integer arithmetic.
  val zeroedBase = CComplexType.getType(base, parseContext).nullValue
  val offset = (this as Expr<Type>).replaceExpr(base, zeroedBase)
  val index = CComplexType.getSignedLong(parseContext).castTo(offset)
  val deref = Dereference(base as Expr<Type>, index as Expr<Type>, elemType.smtType)
  parseContext.metadata.create(deref, "cType", CPointer(null, elemType, parseContext))
  val ref = Reference(deref, ptrType.smtType)
  parseContext.metadata.create(ref, "cType", ptrType)
  return ref
}
