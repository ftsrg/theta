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
package hu.bme.mit.theta.core.serialization

import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.serialization.ObjectTable.Companion.use
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.IfStmt
import hu.bme.mit.theta.core.stmt.LoopStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.OrtStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.ArrayInitExpr
import hu.bme.mit.theta.core.type.ArrayLitExpr
import hu.bme.mit.theta.core.type.ArrayReadExpr
import hu.bme.mit.theta.core.type.ArrayWriteExpr
import hu.bme.mit.theta.core.type.BvConcatExpr
import hu.bme.mit.theta.core.type.BvExtractExpr
import hu.bme.mit.theta.core.type.BvLitExpr
import hu.bme.mit.theta.core.type.BvSignChangeExpr
import hu.bme.mit.theta.core.type.BvToIntExpr
import hu.bme.mit.theta.core.type.BvZExtExpr
import hu.bme.mit.theta.core.type.Dereference
import hu.bme.mit.theta.core.type.EnumLitExpr
import hu.bme.mit.theta.core.type.ExistsExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.FalseExpr
import hu.bme.mit.theta.core.type.ForallExpr
import hu.bme.mit.theta.core.type.ForeignExpr
import hu.bme.mit.theta.core.type.ForeignLitExpr
import hu.bme.mit.theta.core.type.FpAddExpr
import hu.bme.mit.theta.core.type.FpLitExpr
import hu.bme.mit.theta.core.type.FpToBvExpr
import hu.bme.mit.theta.core.type.FuncAppExpr
import hu.bme.mit.theta.core.type.FuncLitExpr
import hu.bme.mit.theta.core.type.IntAddExpr
import hu.bme.mit.theta.core.type.IntLitExpr
import hu.bme.mit.theta.core.type.IntToRatExpr
import hu.bme.mit.theta.core.type.InvalidLitExpr
import hu.bme.mit.theta.core.type.IteExpr
import hu.bme.mit.theta.core.type.PrimeExpr
import hu.bme.mit.theta.core.type.RatLitExpr
import hu.bme.mit.theta.core.type.RefExpr
import hu.bme.mit.theta.core.type.Reference
import hu.bme.mit.theta.core.type.TraceabilityInfo
import hu.bme.mit.theta.core.type.TraceableWrapperExpr
import hu.bme.mit.theta.core.type.TrueExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatType
import java.math.BigInteger
import kotlin.reflect.KClass
import kotlin.reflect.full.isSubclassOf
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.json.Json
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.modules.polymorphic
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertSame
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

@Serializable
@SerialName("label")
private data class LabelInfo(val label: String) : TraceabilityInfo

@Serializable
private class Payload(
  @Serializable(with = ObjectTable.Serializer::class) val table: ObjectTable,
  val exprs: List<Expr<*>>,
  val stmts: List<Stmt>,
  val decls: List<Decl<*>>,
)

@Serializable
private class Roots(val exprs: List<Expr<*>>, val stmts: List<Stmt>, val decls: List<Decl<*>>)

class ObjectTableTest {

  private val module = SerializersModule {
    polymorphic(TraceabilityInfo::class) { subclass(LabelInfo::class, LabelInfo.serializer()) }
  }
  private val json = Json { serializersModule = module }

  private fun bits(vararg b: Int) = BooleanArray(b.size) { b[it] == 1 }

  private fun encode(exprs: List<Expr<*>>, stmts: List<Stmt>, decls: List<Decl<*>>): String {
    val table = ObjectTable.forEncoding(module, CoreTableClasses)
    return table.use {
      table.collect(Roots.serializer(), Roots(exprs, stmts, decls))
      table.complete()
      json.encodeToString(Payload.serializer(), Payload(table, exprs, stmts, decls))
    }
  }

  private fun decode(text: String): Payload =
    ObjectTable.forDecoding(module, CoreTableClasses).use {
      json.decodeFromString(Payload.serializer(), text)
    }

  @Test
  fun everyCoreClassIsATableClass() {
    val roots: List<KClass<*>> = listOf(Expr::class, Stmt::class, Decl::class)
    val concrete =
      roots.flatMap { concreteSubclasses(it) } +
        listOf(
          BoolType::class,
          IntType::class,
          RatType::class,
          BvType::class,
          FpType::class,
          ArrayType::class,
          FuncType::class,
          EnumType::class,
        )
    val missing = concrete.filter { runCatching { CoreTableClasses.of(it.java) }.isFailure }
    assertEquals(emptyList<KClass<*>>(), missing, "classes missing from CoreTableClasses")
    // Each name is that of the class it is listed with.
    val entries = CoreTableClasses.names.associateWith { CoreTableClasses.named(it) }
    assertEquals(entries.keys.toList(), entries.values.map { it.cls.name })
    // A listed object must come with its instance: a format may write nothing for it.
    val objects = entries.values.filter { it.cls.kotlin.objectInstance != null }
    assertEquals(objects.map { it.cls.kotlin.objectInstance }, objects.map { it.instance })
  }

  /** Concrete classes of a sealed hierarchy, without its open extension points. */
  private fun concreteSubclasses(root: KClass<*>): List<KClass<*>> =
    root.sealedSubclasses
      .flatMap { sub ->
        when {
          sub.isSubclassOf(ForeignExpr::class) || sub.isSubclassOf(ForeignLitExpr::class) ->
            emptyList()
          sub.isSealed -> concreteSubclasses(sub)
          sub.isAbstract -> emptyList()
          // An open class such as VarDecl also has (non-serializable, analysis-only) subclasses.
          else -> listOf(sub)
        }
      }
      .distinct()

  @Test
  fun expressionsStatementsAndDeclarationsRoundTrip() {
    val x = Decls.Var("x", IntType)
    val b = Decls.Var("b", BoolType)
    val bv = Decls.Var("bv", BvType.of(8, true))
    val arr = Decls.Var("arr", ArrayType.of(IntType, IntType))
    val p = Decls.Param("p", IntType)
    val c = Decls.Const("c", RatType)
    val traced = Decls.Var("traced", IntType).also { it.traceability = LabelInfo("int x") }
    val indexed = x.getConstDecl(3)

    val color = EnumType.of("Color", listOf("RED", "GREEN"))
    val one = IntLitExpr.of(BigInteger.ONE)
    val sum = IntAddExpr.of(listOf(x.ref, one))
    val bvLit = BvLitExpr.of(bits(1, 0, 1, 1, 0, 0, 1, 0, 1), true)
    val fpLit =
      FpLitExpr.of(
        false,
        BvLitExpr.of(bits(1, 0, 0, 0, 1)),
        BvLitExpr.of(bits(0, 1, 0, 0, 0, 0, 0, 0, 0, 0)),
      )
    val fpType = FpType.of(5, 11)
    val wrapped = TraceableWrapperExpr.of(sum, LabelInfo("x + 1"))
    val deref = Dereference.of(x.ref, one, IntType)

    val exprs: List<Expr<*>> =
      listOf(
        sum,
        RefExpr.of(x),
        IntAddExpr.of(listOf(sum, sum)),
        RatLitExpr.of(BigInteger.valueOf(6), BigInteger.valueOf(-4)),
        bvLit,
        BvExtractExpr.of(
          bv.ref,
          IntLitExpr.of(BigInteger.ZERO),
          IntLitExpr.of(BigInteger.valueOf(4)),
        ),
        BvZExtExpr.of(bv.ref, BvType.of(16)),
        BvSignChangeExpr.of(bv.ref, BvType.of(8, false)),
        BvConcatExpr.of(listOf(bv.ref, bvLit)),
        BvToIntExpr.of(bv.ref, true),
        fpLit,
        FpAddExpr.of(FpRoundingMode.RTZ, listOf(fpLit, fpLit)),
        FpToBvExpr.of(FpRoundingMode.RNE, fpLit, 16, true),
        EnumLitExpr.of(color, "GREEN"),
        EnumLitExpr.of(color, "RED"),
        ArrayReadExpr.of(arr.ref, x.ref),
        ArrayWriteExpr.of(arr.ref, x.ref, one),
        ArrayLitExpr.of(
          listOf(Tuple2.of(one, IntLitExpr.of(BigInteger.TWO))),
          one,
          ArrayType.of(IntType, IntType),
        ),
        ArrayInitExpr.of(listOf(Tuple2.of(x.ref, sum)), one, ArrayType.of(IntType, IntType)),
        IteExpr.of(b.ref, sum, x.ref),
        ForallExpr.of(listOf(p), IntExprs.Gt(p.ref, x.ref)),
        ExistsExpr.of(listOf(p), TrueExpr),
        FuncLitExpr.of(p, IntAddExpr.of(listOf(p.ref, one))),
        FuncAppExpr.of(FuncLitExpr.of(p, p.ref), one),
        IntToRatExpr.of(x.ref),
        PrimeExpr.of(x.ref),
        Reference.of(x.ref, IntType),
        deref,
        deref.withUniquenessExpr(one),
        InvalidLitExpr(IntType),
        FalseExpr,
        wrapped,
        c.ref,
        indexed.ref,
        traced.ref,
      )
    val stmts: List<Stmt> =
      listOf(
        AssignStmt.of(x, sum),
        AssumeStmt.of(b.ref),
        HavocStmt.of(x),
        SkipStmt.getInstance(),
        MemoryAssignStmt.create<IntType>(TraceableWrapperExpr.of(deref, LabelInfo("*x")), sum),
        SequenceStmt.of(listOf(HavocStmt.of(x), AssumeStmt.of(b.ref))),
        NonDetStmt.of(listOf()),
        OrtStmt.of(listOf(SkipStmt.getInstance())),
        IfStmt.of(b.ref, HavocStmt.of(x)),
        LoopStmt.of(HavocStmt.of(x), x, one, one),
      )
    val decls: List<Decl<*>> = listOf(x, b, p, c, indexed, traced)

    val text = encode(exprs, stmts, decls)
    val decoded = decode(text)

    // Declarations are identities, so decoded expressions are compared by their text and by
    // encoding them again.
    // An invalid literal has neither value equality nor a text form.
    val invalid = exprs.indexOfFirst { it is InvalidLitExpr<*> }
    assertEquals(IntType, (decoded.exprs[invalid] as InvalidLitExpr<*>).type)
    val printable = exprs.indices - invalid
    assertEquals(printable.map { "${exprs[it]}" }, printable.map { "${decoded.exprs[it]}" })
    assertEquals(stmts.map { "$it" }, decoded.stmts.map { "$it" })
    assertEquals(decls.map { "$it" }, decoded.decls.map { "$it" })
    assertEquals(text, encode(decoded.exprs, decoded.stmts, decoded.decls))
    // Closed expressions are values.
    assertEquals(exprs[3], decoded.exprs[3])
    assertEquals(exprs[4], decoded.exprs[4])

    val dx = decoded.decls[0] as VarDecl<*>
    // The canonical reference stays the declaration's own; an extra one stays a separate object.
    assertSame(dx.ref, decoded.exprs[0].ops[0])
    assertTrue(decoded.exprs[1] !== dx.ref)
    assertSame(dx, (decoded.exprs[1] as RefExpr<*>).decl)
    // Shared subexpressions stay shared.
    assertSame(decoded.exprs[0], decoded.exprs[2].ops[0])
    assertSame(decoded.exprs[2].ops[0], decoded.exprs[2].ops[1])
    // Wrappers and their info survive, and so does a declaration's traceability.
    val dWrapped = decoded.exprs[exprs.indexOfFirst { it === wrapped }] as TraceableWrapperExpr<*>
    assertEquals(LabelInfo("x + 1"), dWrapped.info)
    assertEquals(LabelInfo("int x"), (decoded.decls[5] as VarDecl<*>).traceability)
    val dStmt = decoded.stmts[4] as MemoryAssignStmt<*, *, *>
    assertTrue(dStmt.tracedDeref is TraceableWrapperExpr<*>)
    assertEquals("$deref", "${dStmt.deref}")
    // An enumeration type is equal only to itself, so its literals must share one decoded type.
    val green = exprs.indexOfFirst { it is EnumLitExpr }
    assertSame(decoded.exprs[green].type, decoded.exprs[green + 1].type)
    assertSame(SkipStmt.getInstance(), decoded.stmts[3])
  }

  @Test
  fun bitsOfAnyWidthRoundTrip() {
    for (width in listOf(1, 3, 4, 5, 8, 31, 64, 65)) {
      val value = BooleanArray(width) { (it * 7 + width) % 3 == 0 }
      val text = Json.encodeToString(BitsSerializer, value)
      assertTrue(value.contentEquals(Json.decodeFromString(BitsSerializer, text)), text)
    }
  }
}
