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
package hu.bme.mit.theta.xcfa.serialization

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.decl.IndexedVarDecl
import hu.bme.mit.theta.core.stmt.IfStmt
import hu.bme.mit.theta.core.stmt.LoopStmt
import hu.bme.mit.theta.core.stmt.OrtStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.frontend.FrontendMetadata
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.serialization.CTypeNode
import hu.bme.mit.theta.xcfa.model.serialization.DeclNode
import hu.bme.mit.theta.xcfa.model.serialization.ExprNode
import hu.bme.mit.theta.xcfa.model.serialization.FrontendMetadataSurrogate
import hu.bme.mit.theta.xcfa.model.serialization.ParseContextSurrogate
import hu.bme.mit.theta.xcfa.model.serialization.StmtNode
import hu.bme.mit.theta.xcfa.model.serialization.TypeNode
import hu.bme.mit.theta.xcfa.model.serialization.XcfaSurrogate
import java.lang.reflect.Field
import java.lang.reflect.Modifier
import java.nio.file.Files
import java.nio.file.Paths
import java.util.zip.ZipFile
import kotlin.io.path.isDirectory
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.descriptors.elementNames
import kotlinx.serialization.serializer
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * The serialization plugin checks the Kotlin model, but not the Java core it refers to, nor that
 * every subclass of a sealed class is serializable. This test does: it fails when a core class
 * gains state or a subclass that the serialization surrogates do not cover.
 */
class XcfaSerializationCoverageTest {

  private fun classesNextTo(anchor: Class<*>, pkg: String): List<Class<*>> {
    val root = Paths.get(anchor.protectionDomain.codeSource.location.toURI())
    val prefix = pkg.replace('.', '/') + "/"
    val names =
      if (root.isDirectory()) {
        Files.walk(root).use { s -> s.map { root.relativize(it).toString() }.toList() }
      } else {
        ZipFile(root.toFile()).use { z -> z.entries().asSequence().map { it.name }.toList() }
      }
    return names
      .filter { it.startsWith(prefix) && it.endsWith(".class") }
      .map { Class.forName(it.removeSuffix(".class").replace('/', '.'), false, anchor.classLoader) }
  }

  private fun Class<*>.concrete() =
    !isInterface && !Modifier.isAbstract(modifiers) && !isAnonymousClass

  private fun Class<*>.stateFields(upTo: Class<*>? = null): List<Field> =
    generateSequence(this) { it.superclass }
      .takeWhile { it != Any::class.java && it != upTo }
      .flatMap { it.declaredFields.asSequence() }
      .filter { !Modifier.isStatic(it.modifiers) && !it.isSynthetic }
      .toList()

  private fun <T> concreteSubclasses(base: Class<T>, pkg: String, vararg extra: Class<*>) =
    (classesNextTo(base, pkg) + extra)
      .filter { base.isAssignableFrom(it) && it.concrete() }
      .distinct()

  // A dedicated surrogate stores exactly these fields; anything new needs a decision.
  private val dedicatedExprFields =
    mapOf(
      "RefExpr" to setOf("decl"),
      "IntLitExpr" to setOf("value"),
      "RatLitExpr" to setOf("num", "denom"),
      "BvLitExpr" to setOf("value", "signed"),
      "FpLitExpr" to setOf("hidden", "exponent", "significand"),
      "EnumLitExpr" to setOf("type", "value"),
      "ArrayLitExpr" to setOf("type", "elems", "elseElem"),
      // ops is the flattened [else, indices, elems] list, rebuilt by the constructor
      "ArrayInitExpr" to setOf("type", "elems", "elseElem", "ops"),
      "InvalidLitExpr" to setOf("type"),
      "Dereference" to setOf("array", "offset", "type", "uniquenessIdx"),
      "Reference" to setOf("expr", "type"),
      "BvZExtExpr" to setOf("op", "extendType"),
      "BvSExtExpr" to setOf("op", "extendType"),
      "BvSignChangeExpr" to setOf("op", "newType"),
      "BvToIntExpr" to setOf("op", "isSigned"),
      "FpAddExpr" to setOf("ops", "roundingMode"),
      "FpMulExpr" to setOf("ops", "roundingMode"),
      "FpSubExpr" to setOf("leftOp", "rightOp", "roundingMode"),
      "FpDivExpr" to setOf("leftOp", "rightOp", "roundingMode"),
      "FpSqrtExpr" to setOf("op", "roundingMode"),
      "FpRoundToIntegralExpr" to setOf("op", "roundingMode"),
      "FpFromBvExpr" to setOf("op", "roundingMode", "fpType", "isSigned"),
      "FpFromIeeeBvExpr" to setOf("op", "fpType"),
      "FpToBvExpr" to setOf("op", "size", "sgn", "roundingMode"),
      "FpToFpExpr" to setOf("op", "expBits", "signBits", "roundingMode"),
      "ForallExpr" to setOf("paramDecls", "op"),
      "ExistsExpr" to setOf("paramDecls", "op"),
      "FuncLitExpr" to setOf("param", "result"),
      "TrueExpr" to setOf(),
      "FalseExpr" to setOf(),
      "UnsupportedInitializer" to setOf(),
    )

  // Lazily computed hash codes and cached values are derived, not state.
  private fun Field.isCache() = name == "hashCode" || name == "hash"

  @Test
  fun everyExpressionClassIsCovered() {
    val problems = ArrayList<String>()
    val exprs =
      concreteSubclasses(
        Expr::class.java,
        "hu.bme.mit.theta.core.type",
        UnsupportedInitializer::class.java,
      )
    assertTrue(exprs.size > 100, "class scan found only ${exprs.size} expression classes")
    for (cls in exprs) {
      val fields = cls.stateFields().filterNot { it.isCache() }
      if (cls in ExprNode.DEDICATED) {
        val expected = dedicatedExprFields[cls.simpleName]
        val actual = fields.map { it.name }.toSet()
        if (expected != actual)
          problems.add("${cls.name}: fields $actual, surrogate covers $expected")
        continue
      }
      val state =
        fields.filterNot {
          Expr::class.java.isAssignableFrom(it.type) || List::class.java.isAssignableFrom(it.type)
        }
      if (state.isNotEmpty()) {
        problems.add("${cls.name} has state besides its ops: ${state.map { it.name }}")
      }
      val factory =
        cls.declaredMethods.any {
          Modifier.isStatic(it.modifiers) &&
            (it.name == "create" || it.name == "of" || it.name == "getInstance") &&
            (it.parameterTypes.all { p -> p.isAssignableFrom(Expr::class.java) } ||
              (it.parameterCount == 1 && it.parameterTypes[0].isAssignableFrom(List::class.java)))
        }
      if (!factory) problems.add("${cls.name} has no ops-only static factory")
    }
    assertTrue(problems.isEmpty(), problems.joinToString("\n"))
  }

  @Test
  fun everyTypeDeclAndStatementClassIsCovered() {
    val types = concreteSubclasses(Type::class.java, "hu.bme.mit.theta.core.type")
    assertEquals(emptyList<Class<*>>(), types.filter { it !in TypeNode.SUPPORTED })

    // Indexed declarations only exist inside solvers (unfolded paths), never in an XCFA.
    val decls = concreteSubclasses(Decl::class.java, "hu.bme.mit.theta.core.decl")
    val notInXcfa = setOf(IndexedVarDecl::class.java, IndexedConstDecl::class.java)
    assertEquals(
      emptyList<Class<*>>(),
      decls.filter {
        it !in DeclNode.SUPPORTED && it !in notInXcfa && it.simpleName != "BasicConstDecl"
      },
    )

    // Structured statements are CFA/STS-level; XCFA labels encode control flow as edges.
    val stmts = concreteSubclasses(Stmt::class.java, "hu.bme.mit.theta.core.stmt")
    val structured = setOf(IfStmt::class.java, LoopStmt::class.java, OrtStmt::class.java)
    assertEquals(
      emptyList<Class<*>>(),
      stmts.filter { it !in StmtNode.SUPPORTED && it !in structured },
    )
  }

  @Test
  fun everyCTypeClassIsCovered() {
    val base = CComplexType::class.java
    assertEquals(
      CTypeNode.BASE_FIELDS,
      base.declaredFields.filter { !Modifier.isStatic(it.modifiers) }.map { it.name }.toSet(),
    )
    val problems = ArrayList<String>()
    val ctypes =
      concreteSubclasses(base, "hu.bme.mit.theta.frontend.transformation.model.types.complex")
    assertTrue(ctypes.size > 20, "class scan found only ${ctypes.size} C type classes")
    for (cls in ctypes) {
      val own =
        cls.stateFields(upTo = base).map { it.name }.toSet() - CTypeNode.CONSTRUCTOR_DERIVED_FIELDS
      when (cls) {
        CPointer::class.java ->
          if (own != setOf("embeddedType", "isFunctionPointer"))
            problems.add("${cls.name}: fields $own")
        CArray::class.java ->
          if (own != setOf("embeddedType", "arrayDimension"))
            problems.add("${cls.name}: fields $own")
        CStruct::class.java -> {
          val covered =
            setOf(
              "fields",
              "isUnion",
              "bitfieldWidths",
              "paddings",
              "attributes",
              "fieldAttributes",
            )
          if (own != covered + CTypeNode.STRUCT_DERIVED_FIELDS)
            problems.add("${cls.name}: fields $own")
        }
        else -> {
          if (own.isNotEmpty()) problems.add("${cls.name} has state of its own: $own")
          runCatching { cls.getConstructor(CSimpleType::class.java, ParseContext::class.java) }
            .onFailure {
              problems.add("${cls.name} has no (CSimpleType, ParseContext) constructor")
            }
        }
      }
    }
    assertTrue(problems.isEmpty(), problems.joinToString("\n"))
  }

  @Test
  fun parseContextAndXcfaFieldsAreCovered() {
    fun fields(c: Class<*>) =
      c.declaredFields.filter { !Modifier.isStatic(it.modifiers) }.map { it.name }.toSet()
    assertEquals(ParseContextSurrogate.COVERED, fields(ParseContext::class.java))
    assertEquals(FrontendMetadataSurrogate.COVERED, fields(FrontendMetadata::class.java))
    assertEquals(
      XcfaSurrogate.COVERED_FIELDS + XcfaSurrogate.DERIVED_FIELDS,
      fields(XCFA::class.java),
    )
  }

  @OptIn(ExperimentalSerializationApi::class)
  @Test
  fun everyLabelIsInTheSealedSerializer() {
    val labels = concreteSubclasses(XcfaLabel::class.java, "hu.bme.mit.theta.xcfa.model")
    val registered = XcfaLabel.serializer().descriptor.getElementDescriptor(1).elementNames.toSet()
    val missing =
      labels.filter {
        val name = runCatching { serializer(it).descriptor.serialName }.getOrNull()
        name == null || name !in registered
      }
    assertEquals(emptyList<Class<*>>(), missing)
  }
}
