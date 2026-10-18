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
package hu.bme.mit.theta.xcfa.model.serialization

import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.ArrayInitExpr
import hu.bme.mit.theta.core.type.ArrayLitExpr
import hu.bme.mit.theta.core.type.BvLitExpr
import hu.bme.mit.theta.core.type.BvSExtExpr
import hu.bme.mit.theta.core.type.BvSignChangeExpr
import hu.bme.mit.theta.core.type.BvToIntExpr
import hu.bme.mit.theta.core.type.BvZExtExpr
import hu.bme.mit.theta.core.type.Dereference
import hu.bme.mit.theta.core.type.EnumLitExpr
import hu.bme.mit.theta.core.type.ExistsExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.FalseExpr
import hu.bme.mit.theta.core.type.ForallExpr
import hu.bme.mit.theta.core.type.FpAddExpr
import hu.bme.mit.theta.core.type.FpDivExpr
import hu.bme.mit.theta.core.type.FpFromBvExpr
import hu.bme.mit.theta.core.type.FpFromIeeeBvExpr
import hu.bme.mit.theta.core.type.FpLitExpr
import hu.bme.mit.theta.core.type.FpMulExpr
import hu.bme.mit.theta.core.type.FpRoundToIntegralExpr
import hu.bme.mit.theta.core.type.FpSqrtExpr
import hu.bme.mit.theta.core.type.FpSubExpr
import hu.bme.mit.theta.core.type.FpToBvExpr
import hu.bme.mit.theta.core.type.FpToFpExpr
import hu.bme.mit.theta.core.type.FuncLitExpr
import hu.bme.mit.theta.core.type.IntLitExpr
import hu.bme.mit.theta.core.type.InvalidLitExpr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.MultiaryExpr
import hu.bme.mit.theta.core.type.QuantifiedExpr
import hu.bme.mit.theta.core.type.RatLitExpr
import hu.bme.mit.theta.core.type.RefExpr
import hu.bme.mit.theta.core.type.Reference
import hu.bme.mit.theta.core.type.TrueExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType
import java.lang.reflect.Constructor
import java.lang.reflect.Field
import java.lang.reflect.Method
import java.lang.reflect.Modifier
import java.math.BigInteger
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

// The core model is Java, which the serialization plugin cannot see; these surrogates are the
// serializable shape of it. XcfaSerializationCoverageTest fails when a core class gains state or
// a subclass that they do not cover.

@Serializable
sealed class TypeNode {

  @Serializable @SerialName("bool") data object Bool : TypeNode()

  @Serializable @SerialName("int") data object Int : TypeNode()

  @Serializable @SerialName("rat") data object Rat : TypeNode()

  @Serializable
  @SerialName("bv")
  data class Bv(val size: kotlin.Int, val signed: Boolean?) : TypeNode()

  @Serializable
  @SerialName("fp")
  data class Fp(val exponent: kotlin.Int, val significand: kotlin.Int) : TypeNode()

  @Serializable
  @SerialName("array")
  data class Array(val index: TypeNode, val elem: TypeNode) : TypeNode()

  @Serializable
  @SerialName("func")
  data class Func(val param: TypeNode, val result: TypeNode) : TypeNode()

  @Serializable
  @SerialName("enum")
  data class Enum(val name: String, val values: List<String>) : TypeNode()

  fun toType(): Type =
    when (this) {
      Bool -> BoolType.getInstance()
      Int -> IntType.getInstance()
      Rat -> RatType.getInstance()
      is Bv -> BvType.of(size, signed)
      is Fp -> FpType.of(exponent, significand)
      is Array -> ArrayType.of(index.toType(), elem.toType())
      is Func -> FuncType.of(param.toType(), result.toType())
      is Enum -> EnumType.of(name, values)
    }

  companion object {

    val SUPPORTED: Set<Class<out Type>> =
      setOf(
        BoolType::class.java,
        IntType::class.java,
        RatType::class.java,
        BvType::class.java,
        FpType::class.java,
        ArrayType::class.java,
        FuncType::class.java,
        EnumType::class.java,
      )

    fun of(t: Type): TypeNode =
      when (t) {
        is BoolType -> Bool
        is IntType -> Int
        is RatType -> Rat
        is BvType -> Bv(t.size, t.signedness)
        is FpType -> Fp(t.exponent, t.significand)
        is ArrayType<*, *> -> Array(of(t.indexType), of(t.elemType))
        is FuncType<*, *> -> Func(of(t.paramType), of(t.resultType))
        is EnumType -> Enum(t.name, t.values.toList())
        else -> error("Unsupported type ${t.javaClass.name}: $t")
      }
  }
}

@Serializable
data class DeclNode(val kind: Kind, val name: String, val type: TypeNode) {

  enum class Kind {
    VAR,
    PARAM,
    CONST,
  }

  fun toDecl(types: MutableMap<TypeNode, Type>): Decl<*> {
    val t = types.getOrPut(type) { type.toType() }
    return when (kind) {
      Kind.VAR -> Decls.Var(name, t)
      Kind.PARAM -> Decls.Param(name, t)
      Kind.CONST -> Decls.Const(name, t)
    }
  }

  companion object {

    val SUPPORTED: Set<Class<*>> =
      setOf(VarDecl::class.java, ParamDecl::class.java, ConstDecl::class.java)

    fun of(d: Decl<*>): DeclNode {
      val kind =
        when (d.javaClass) {
          VarDecl::class.java -> Kind.VAR
          ParamDecl::class.java -> Kind.PARAM
          ConstDecl::class.java -> Kind.CONST
          else -> error("Unsupported declaration ${d.javaClass.name}: $d")
        }
      return DeclNode(kind, d.name, TypeNode.of(d.type))
    }
  }
}

/** Child expressions, declarations and classes are indices into the session's tables. */
@Serializable
sealed class ExprNode {

  @Serializable
  @SerialName("ref")
  data class Ref(val decl: Int, val canonical: Boolean) : ExprNode()

  @Serializable @SerialName("bool") data class BoolLit(val value: Boolean) : ExprNode()

  @Serializable @SerialName("int") data class IntLit(val value: String) : ExprNode()

  @Serializable
  @SerialName("rat")
  data class RatLit(val num: String, val denom: String) : ExprNode()

  @Serializable
  @SerialName("bv")
  class BvLit(val signed: Boolean?, val size: Int, val words: IntArray) : ExprNode()

  @Serializable
  @SerialName("fp")
  data class FpLit(val hidden: Boolean, val exponent: Int, val significand: Int) : ExprNode()

  @Serializable
  @SerialName("enum")
  data class EnumLit(val type: TypeNode, val value: String) : ExprNode()

  @Serializable
  @SerialName("arrayLit")
  class ArrayLit(val type: TypeNode, val indices: IntArray, val elems: IntArray, val elze: Int) :
    ExprNode()

  @Serializable
  @SerialName("arrayInit")
  class ArrayInit(val type: TypeNode, val indices: IntArray, val elems: IntArray, val elze: Int) :
    ExprNode()

  @Serializable @SerialName("invalid") data class Invalid(val type: TypeNode) : ExprNode()

  @Serializable
  @SerialName("deref")
  data class Deref(val array: Int, val offset: Int, val uniqueness: Int?, val type: TypeNode) :
    ExprNode()

  @Serializable
  @SerialName("reference")
  data class Reference(val expr: Int, val type: TypeNode) : ExprNode()

  @Serializable @SerialName("zext") data class ZExt(val op: Int, val type: TypeNode) : ExprNode()

  @Serializable @SerialName("sext") data class SExt(val op: Int, val type: TypeNode) : ExprNode()

  @Serializable
  @SerialName("signChange")
  data class SignChange(val op: Int, val type: TypeNode) : ExprNode()

  @Serializable
  @SerialName("bvToInt")
  data class BvToInt(val op: Int, val signed: Boolean) : ExprNode()

  /** FpAdd/Mul/Sub/Div/Sqrt/RoundToIntegral: ops plus a rounding mode (ordinal, -1 for none). */
  @Serializable
  @SerialName("fpRounded")
  class FpRounded(val cls: Int, val roundingMode: Int, val ops: IntArray) : ExprNode()

  @Serializable
  @SerialName("fpFromBv")
  data class FpFromBv(val roundingMode: Int, val op: Int, val type: TypeNode, val signed: Boolean) :
    ExprNode()

  @Serializable
  @SerialName("fpFromIeeeBv")
  data class FpFromIeeeBv(val op: Int, val type: TypeNode) : ExprNode()

  @Serializable
  @SerialName("fpToBv")
  data class FpToBv(val roundingMode: Int, val op: Int, val size: Int, val signed: Boolean) :
    ExprNode()

  @Serializable
  @SerialName("fpToFp")
  data class FpToFp(val roundingMode: Int, val op: Int, val exponent: Int, val significand: Int) :
    ExprNode()

  @Serializable
  @SerialName("quantified")
  class Quantified(val forall: Boolean, val params: IntArray, val op: Int) : ExprNode()

  @Serializable
  @SerialName("funcLit")
  data class FuncLit(val param: Int, val result: Int) : ExprNode()

  @Serializable @SerialName("unsupportedInit") data object UnsupportedInit : ExprNode()

  /** Any expression whose only state is its ops, rebuilt through its static factory. */
  @Serializable @SerialName("ops") class Ops(val cls: Int, val ops: IntArray) : ExprNode()

  companion object {

    /** Classes with a dedicated node; every other expression class must be ops-only. */
    val DEDICATED: Set<Class<*>> =
      setOf(
        RefExpr::class.java,
        TrueExpr::class.java,
        FalseExpr::class.java,
        IntLitExpr::class.java,
        RatLitExpr::class.java,
        BvLitExpr::class.java,
        FpLitExpr::class.java,
        EnumLitExpr::class.java,
        ArrayLitExpr::class.java,
        ArrayInitExpr::class.java,
        InvalidLitExpr::class.java,
        Dereference::class.java,
        hu.bme.mit.theta.core.type.Reference::class.java,
        BvZExtExpr::class.java,
        BvSExtExpr::class.java,
        BvSignChangeExpr::class.java,
        BvToIntExpr::class.java,
        FpAddExpr::class.java,
        FpMulExpr::class.java,
        FpSubExpr::class.java,
        FpDivExpr::class.java,
        FpSqrtExpr::class.java,
        FpRoundToIntegralExpr::class.java,
        FpFromBvExpr::class.java,
        FpFromIeeeBvExpr::class.java,
        FpToBvExpr::class.java,
        FpToFpExpr::class.java,
        ForallExpr::class.java,
        ExistsExpr::class.java,
        FuncLitExpr::class.java,
        UnsupportedInitializer::class.java,
      )

    private fun rm(mode: FpRoundingMode?) = mode?.ordinal ?: -1

    fun of(e: Expr<*>, s: XcfaSerializationSession): ExprNode {
      fun id(x: Expr<*>) = s.exprId(x)
      fun ops() = IntArray(e.ops.size) { id(e.ops[it]) }
      return when (e) {
        is RefExpr<*> -> Ref(s.declId(e.decl), e === e.decl.ref)
        is TrueExpr -> BoolLit(true)
        is FalseExpr -> BoolLit(false)
        is IntLitExpr -> IntLit(e.value.toString())
        is RatLitExpr -> RatLit(e.num.toString(), e.denom.toString())
        is BvLitExpr -> {
          val bits = e.value
          val words = IntArray((bits.size + 31) / 32)
          for (i in bits.indices) if (bits[i]) words[i / 32] = words[i / 32] or (1 shl (i % 32))
          BvLit(e.type.signedness, bits.size, words)
        }
        is FpLitExpr -> FpLit(e.hidden, id(e.exponent), id(e.significand))
        is EnumLitExpr -> EnumLit(TypeNode.of(e.type), e.value)
        is ArrayLitExpr<*, *> ->
          ArrayLit(
            TypeNode.of(e.type),
            e.elements.map { id(it.get1()) }.toIntArray(),
            e.elements.map { id(it.get2()) }.toIntArray(),
            id(e.elseElem),
          )
        is ArrayInitExpr<*, *> ->
          ArrayInit(
            TypeNode.of(e.type),
            e.elements.map { id(it.get1()) }.toIntArray(),
            e.elements.map { id(it.get2()) }.toIntArray(),
            id(e.elseElem),
          )
        is InvalidLitExpr<*> -> Invalid(TypeNode.of(e.type))
        is Dereference<*, *, *> ->
          Deref(
            id(e.array),
            id(e.offset),
            e.uniquenessIdx.map { id(it) }.orElse(null),
            TypeNode.of(e.type),
          )
        is hu.bme.mit.theta.core.type.Reference<*, *> -> Reference(id(e.expr), TypeNode.of(e.type))
        is BvZExtExpr -> ZExt(id(e.op), TypeNode.of(e.extendType))
        is BvSExtExpr -> SExt(id(e.op), TypeNode.of(e.extendType))
        is BvSignChangeExpr -> SignChange(id(e.op), TypeNode.of(e.type))
        is BvToIntExpr -> BvToInt(id(e.op), e.isSigned)
        is FpAddExpr -> FpRounded(s.classId(e.javaClass), rm(e.roundingMode), ops())
        is FpMulExpr -> FpRounded(s.classId(e.javaClass), rm(e.roundingMode), ops())
        is FpSubExpr -> FpRounded(s.classId(e.javaClass), rm(e.roundingMode), ops())
        is FpDivExpr -> FpRounded(s.classId(e.javaClass), rm(e.roundingMode), ops())
        is FpSqrtExpr -> FpRounded(s.classId(e.javaClass), rm(e.roundingMode), ops())
        is FpRoundToIntegralExpr -> FpRounded(s.classId(e.javaClass), rm(e.roundingMode), ops())
        is FpFromBvExpr -> FpFromBv(rm(e.roundingMode), id(e.op), TypeNode.of(e.fpType), e.isSigned)
        is FpFromIeeeBvExpr -> FpFromIeeeBv(id(e.op), TypeNode.of(e.fpType))
        is FpToBvExpr -> FpToBv(rm(e.roundingMode), id(e.op), e.size, e.sgn)
        is FpToFpExpr -> FpToFp(rm(e.roundingMode), id(e.op), e.expBits, e.signBits)
        is QuantifiedExpr ->
          Quantified(e is ForallExpr, e.paramDecls.map { s.declId(it) }.toIntArray(), id(e.op))
        is FuncLitExpr<*, *> -> FuncLit(s.declId(e.param), id(e.result))
        is UnsupportedInitializer -> UnsupportedInit
        else -> Ops(s.classId(e.javaClass), ops())
      }
    }
  }

  @Suppress("UNCHECKED_CAST")
  fun toExpr(s: XcfaSerializationSession, types: MutableMap<TypeNode, Type>): Expr<*> {
    fun e(i: Int) = s.exprs[i]
    fun t(n: TypeNode) = types.getOrPut(n) { n.toType() }
    fun rm(i: Int) = if (i == -1) null else FpRoundingMode.entries[i]
    return when (this) {
      is Ref -> if (canonical) s.decls[decl].ref else RefExpr.of(s.decls[decl])
      is BoolLit -> if (value) BoolExprs.True() else BoolExprs.False()
      is IntLit -> IntLitExpr.of(BigInteger(value))
      is RatLit -> RatLitExpr.of(BigInteger(num), BigInteger(denom))
      is BvLit ->
        BvLitExpr.of(BooleanArray(size) { words[it / 32] ushr (it % 32) and 1 == 1 }, signed)
      is FpLit -> FpLitExpr.of(hidden, e(exponent) as BvLitExpr, e(significand) as BvLitExpr)
      is EnumLit -> EnumLitExpr.of(t(type) as EnumType, value)
      is ArrayLit ->
        ArrayLitExpr.of(
          indices.indices.map {
            Tuple2.of(e(indices[it]) as LitExpr<Type>, e(elems[it]) as LitExpr<Type>)
          },
          e(elze) as LitExpr<Type>,
          t(type) as ArrayType<Type, Type>,
        )
      is ArrayInit ->
        ArrayInitExpr.of(
          indices.indices.map {
            Tuple2.of(e(indices[it]) as Expr<Type>, e(elems[it]) as Expr<Type>)
          },
          e(elze) as Expr<Type>,
          t(type) as ArrayType<Type, Type>,
        )
      is Invalid -> InvalidLitExpr(t(type))
      is Deref -> {
        val deref = Dereference.of(e(array) as Expr<Type>, e(offset) as Expr<Type>, t(type))
        if (uniqueness == null) deref else deref.withUniquenessExpr(e(uniqueness) as Expr<IntType>)
      }
      is Reference -> hu.bme.mit.theta.core.type.Reference.of(e(expr) as Expr<Type>, t(type))
      is ZExt -> BvZExtExpr.create(e(op), t(type) as BvType)
      is SExt -> BvSExtExpr.create(e(op), t(type) as BvType)
      is SignChange -> BvSignChangeExpr.create(e(op), t(type) as BvType)
      is BvToInt -> BvToIntExpr.create(e(op), signed)
      is FpRounded -> {
        val mode = rm(roundingMode)
        val args = ops.map { e(it) }
        when (s.classes[cls]) {
          FpAddExpr::class.java -> FpAddExpr.create(mode!!, args)
          FpMulExpr::class.java -> FpMulExpr.create(mode!!, args)
          FpSubExpr::class.java -> FpSubExpr.create(mode, args[0], args[1])
          FpDivExpr::class.java -> FpDivExpr.create(mode, args[0], args[1])
          FpSqrtExpr::class.java -> FpSqrtExpr.create(mode!!, args[0])
          FpRoundToIntegralExpr::class.java -> FpRoundToIntegralExpr.create(mode!!, args[0])
          else -> error("Not a rounded floating-point expression: ${s.classes[cls]}")
        }
      }
      is FpFromBv ->
        FpFromBvExpr.create(rm(roundingMode)!!, e(op) as Expr<BvType>, t(type) as FpType, signed)
      is FpFromIeeeBv -> FpFromIeeeBvExpr.create(e(op) as Expr<BvType>, t(type) as FpType)
      is FpToBv -> FpToBvExpr.create(rm(roundingMode)!!, e(op) as Expr<FpType>, size, signed)
      is FpToFp ->
        FpToFpExpr.create(rm(roundingMode)!!, e(op) as Expr<FpType>, exponent, significand)
      is Quantified -> {
        val paramDecls = params.map { s.decls[it] as ParamDecl<*> }
        if (forall) ForallExpr.create(paramDecls, e(op)) else ExistsExpr.create(paramDecls, e(op))
      }
      is FuncLit -> FuncLitExpr.of(s.decls[param] as ParamDecl<Type>, e(result) as Expr<Type>)
      UnsupportedInit -> UnsupportedInitializer()
      is Ops -> OpsFactory.of(s.classes[cls], ops.size).create(ops.map { e(it) })
    }
  }
}

/** Calls the static `create`/`of` factory of an expression class whose only state is its ops. */
class OpsFactory private constructor(cls: Class<*>, arity: Int) {

  private val method: Method
  private val takesList: Boolean

  init {
    val candidates =
      cls.declaredMethods.filter {
        Modifier.isStatic(it.modifiers) &&
          Modifier.isPublic(it.modifiers) &&
          (it.name == "create" || it.name == "of" || it.name == "getInstance") &&
          cls.isAssignableFrom(it.returnType)
      }
    val listFactory =
      candidates.firstOrNull {
        it.parameterCount == 1 && it.parameterTypes[0].isAssignableFrom(List::class.java)
      }
    val arityFactory =
      candidates
        .filter {
          it.parameterCount == arity &&
            it.parameterTypes.all { p -> p.isAssignableFrom(Expr::class.java) }
        }
        .minByOrNull { if (it.name == "create") 0 else 1 }
    val preferList = MultiaryExpr::class.java.isAssignableFrom(cls)
    method =
      (if (preferList) listFactory ?: arityFactory else arityFactory ?: listFactory)
        ?: error("No ops-only factory for ${cls.name} with $arity ops")
    takesList = method === listFactory
  }

  fun create(ops: List<Expr<*>>): Expr<*> =
    (if (takesList) method.invoke(null, ops) else method.invoke(null, *ops.toTypedArray()))
      as Expr<*>

  companion object {
    private val cache = java.util.concurrent.ConcurrentHashMap<Pair<Class<*>, Int>, OpsFactory>()

    fun of(cls: Class<*>, arity: Int): OpsFactory =
      cache.computeIfAbsent(cls to arity) { OpsFactory(it.first, it.second) }
  }
}

@Serializable
sealed class StmtNode {

  @Serializable @SerialName("assign") data class Assign(val decl: Int, val expr: Int) : StmtNode()

  @Serializable @SerialName("assume") data class Assume(val cond: Int) : StmtNode()

  @Serializable @SerialName("havoc") data class Havoc(val decl: Int) : StmtNode()

  @Serializable @SerialName("skip") data object Skip : StmtNode()

  @Serializable
  @SerialName("memoryAssign")
  data class MemoryAssign(val deref: Int, val expr: Int) : StmtNode()

  @Serializable @SerialName("sequence") class Sequence(val stmts: IntArray) : StmtNode()

  @Serializable @SerialName("nondet") class NonDet(val stmts: IntArray) : StmtNode()

  @Suppress("UNCHECKED_CAST")
  fun toStmt(s: XcfaSerializationSession): Stmt =
    when (this) {
      is Assign -> AssignStmt.of(s.decls[decl] as VarDecl<Type>, s.exprs[expr] as Expr<Type>)
      is Assume -> AssumeStmt.of(s.exprs[cond] as Expr<BoolType>)
      is Havoc -> HavocStmt.of(s.decls[decl] as VarDecl<*>)
      Skip -> SkipStmt.getInstance()
      is MemoryAssign ->
        MemoryAssignStmt.create(
          s.exprs[deref] as Dereference<Type, Type, *>,
          s.exprs[expr] as Expr<Type>,
        )
      is Sequence -> SequenceStmt.of(stmts.map { s.stmts[it] })
      is NonDet -> NonDetStmt.of(stmts.map { s.stmts[it] })
    }

  companion object {

    val SUPPORTED: Set<Class<*>> =
      setOf(
        AssignStmt::class.java,
        AssumeStmt::class.java,
        HavocStmt::class.java,
        SkipStmt::class.java,
        MemoryAssignStmt::class.java,
        SequenceStmt::class.java,
        NonDetStmt::class.java,
      )

    fun of(st: Stmt, s: XcfaSerializationSession): StmtNode =
      when (st) {
        is AssignStmt<*> -> Assign(s.declId(st.varDecl), s.exprId(st.expr))
        is AssumeStmt -> Assume(s.exprId(st.cond))
        is HavocStmt<*> -> Havoc(s.declId(st.varDecl))
        is SkipStmt -> Skip
        is MemoryAssignStmt<*, *, *> -> MemoryAssign(s.exprId(st.deref), s.exprId(st.expr))
        is SequenceStmt -> Sequence(st.stmts.map { s.stmtId(it) }.toIntArray())
        is NonDetStmt -> NonDet(st.stmts.map { s.stmtId(it) }.toIntArray())
        else -> error("Unsupported statement ${st.javaClass.name}: $st")
      }
  }
}

/**
 * A C type. [CComplexType.getOrigin] (the declaration-side simple type) is not kept: it is only
 * read while parsing.
 */
@Serializable
sealed class CTypeNode {
  abstract val threadLocal: Boolean
  abstract val atomic: Boolean

  /** A type whose only state is in [CComplexType] itself (integers, reals, void, function). */
  @Serializable
  @SerialName("simple")
  data class Simple(
    val cls: String,
    override val threadLocal: Boolean,
    override val atomic: Boolean,
  ) : CTypeNode()

  @Serializable
  @SerialName("pointer")
  data class Pointer(
    /** Null for a pointer whose pointee is not known (e.g. the generic stack pointer). */
    val embedded: Int?,
    val functionPointer: Boolean,
    override val threadLocal: Boolean,
    override val atomic: Boolean,
  ) : CTypeNode()

  @Serializable
  @SerialName("array")
  data class Array(
    val embedded: Int,
    val dimension: Int?,
    override val threadLocal: Boolean,
    override val atomic: Boolean,
  ) : CTypeNode()

  @Serializable
  @SerialName("struct")
  data class Struct(
    val union: Boolean,
    val fields: List<Field>,
    val bitfieldWidths: List<Int>,
    val paddings: List<Padding>,
    val attributes: Attributes,
    val fieldAttributes: List<Attributes>,
    override val threadLocal: Boolean,
    override val atomic: Boolean,
  ) : CTypeNode()

  @Serializable data class Field(val name: String, val type: Int)

  @Serializable data class Padding(val afterFieldIndex: Int, val bitWidth: Int, val baseBits: Int)

  @Serializable
  data class Attributes(val packed: Boolean, val alignedToBits: Int) {
    fun toAttributes() = ObjectLayout.Attributes(packed, alignedToBits)
  }

  fun toCType(s: XcfaSerializationSession): CComplexType {
    val pc = s.parseContext
    val t =
      when (this) {
        is Simple ->
          constructors
            .computeIfAbsent(cls) {
              Class.forName(it).getConstructor(CSimpleType::class.java, ParseContext::class.java)
            }
            .newInstance(null, pc) as CComplexType
        is Pointer ->
          CPointer(null, embedded?.let { s.ctypes[it] }, pc).also {
            it.isFunctionPointer = functionPointer
          }
        is Array -> CArray(null, s.ctypes[embedded], pc, dimension?.let { CExpr(s.exprs[it], pc) })
        is Struct ->
          CStruct(
            null,
            fields.map { Tuple2.of(it.name, s.ctypes[it.type]) },
            union,
            pc,
            bitfieldWidths,
            paddings.map { CStruct.Padding(it.afterFieldIndex, it.bitWidth, it.baseBits) },
            attributes.toAttributes(),
            fieldAttributes.map { it.toAttributes() },
          )
      }
    if (threadLocal) t.setThreadLocal()
    if (atomic) t.setAtomic()
    return t
  }

  companion object {
    private val constructors = java.util.concurrent.ConcurrentHashMap<String, Constructor<*>>()

    /** Fields of [CComplexType] itself; `origin` and `parseContext` are restored, not stored. */
    val BASE_FIELDS = setOf("origin", "threadLocal", "atomic", "parseContext")

    val DEDICATED: Set<Class<*>> =
      setOf(CPointer::class.java, CArray::class.java, CStruct::class.java)

    private fun privateField(name: String) =
      CStruct::class.java.getDeclaredField(name).apply { isAccessible = true }

    private val STRUCT_BITFIELD_WIDTHS = privateField("bitfieldWidths")
    private val STRUCT_FIELD_ATTRIBUTES = privateField("fieldAttributes")

    /** Constants that each concrete integer/real class assigns in its constructor. */
    val CONSTRUCTOR_DERIVED_FIELDS = setOf("rank", "unsigned")

    /** CStruct fields that are derived from the stored ones in its constructor. */
    val STRUCT_DERIVED_FIELDS = setOf("slots", "layoutUnitCount")

    @Suppress("UNCHECKED_CAST")
    fun of(t: CComplexType, s: XcfaSerializationSession): CTypeNode =
      when (t) {
        is CPointer ->
          Pointer(
            t.embeddedType?.let { s.ctypeId(it) },
            t.isFunctionPointer,
            t.isThreadLocal,
            t.isAtomic,
          )
        is CArray ->
          Array(
            s.ctypeId(t.embeddedType),
            t.arrayDimension?.expression?.let { s.exprId(it) },
            t.isThreadLocal,
            t.isAtomic,
          )
        is CStruct ->
          Struct(
            t.isUnion,
            t.fields.map { Field(it.get1(), s.ctypeId(it.get2())) },
            STRUCT_BITFIELD_WIDTHS.get(t) as List<Int>,
            t.paddings.map { Padding(it.afterFieldIndex, it.bitWidth, it.baseBits) },
            Attributes(t.attributes.packed, t.attributes.alignedToBits),
            (STRUCT_FIELD_ATTRIBUTES.get(t) as List<ObjectLayout.Attributes>).map {
              Attributes(it.packed, it.alignedToBits)
            },
            t.isThreadLocal,
            t.isAtomic,
          )
        else -> Simple(t.javaClass.name, t.isThreadLocal, t.isAtomic)
      }
  }
}
