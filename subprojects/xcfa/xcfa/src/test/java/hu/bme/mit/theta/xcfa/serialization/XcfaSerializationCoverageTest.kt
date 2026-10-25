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

import hu.bme.mit.theta.core.type.ForeignExpr
import hu.bme.mit.theta.core.type.ForeignLitExpr
import hu.bme.mit.theta.frontend.FrontendMetadata
import hu.bme.mit.theta.frontend.FrontendTableClasses
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.LaidOutValue
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.serialization.FrontendMetadataSurrogate
import hu.bme.mit.theta.xcfa.model.serialization.XcfaSerialization
import hu.bme.mit.theta.xcfa.model.serialization.XcfaSurrogate
import hu.bme.mit.theta.xcfa.utils.MallocLitExpr
import java.lang.reflect.Modifier
import java.nio.file.Files
import java.nio.file.Paths
import java.util.zip.ZipFile
import kotlin.io.path.invariantSeparatorsPathString
import kotlin.io.path.isDirectory
import kotlin.reflect.KClass
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.elementNames
import kotlinx.serialization.serializer
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * The serialization plugin checks the fields of the classes it serializes, but not that every
 * subclass is serializable, that references stay references, nor the classes that still go through
 * surrogates (the parse context, the XCFA itself). This test does.
 */
class XcfaSerializationCoverageTest {

  private fun classesNextTo(anchor: Class<*>, pkg: String): List<Class<*>> {
    val root = Paths.get(anchor.protectionDomain.codeSource.location.toURI())
    val prefix = pkg.replace('.', '/') + "/"
    val names =
      if (root.isDirectory()) {
        Files.walk(root).use { s ->
          s.map { root.relativize(it).invariantSeparatorsPathString }.toList()
        }
      } else {
        ZipFile(root.toFile()).use { z -> z.entries().asSequence().map { it.name }.toList() }
      }
    return names
      .filter { it.startsWith(prefix) && it.endsWith(".class") }
      .map { Class.forName(it.removeSuffix(".class").replace('/', '.'), false, anchor.classLoader) }
  }

  private fun Class<*>.concrete() =
    !isInterface && !Modifier.isAbstract(modifiers) && !isAnonymousClass

  private fun <T> concreteSubclasses(base: Class<T>, pkg: String, vararg extra: Class<*>) =
    (classesNextTo(base, pkg) + extra)
      .filter { base.isAssignableFrom(it) && it.concrete() }
      .distinct()

  @Test
  fun everyForeignExpressionIsATableClass() {
    // Core's own classes are covered by ObjectTableTest; these extend it from outside.
    val foreign =
      (classesNextTo(MallocLitExpr::class.java, "hu.bme.mit.theta.xcfa") +
          classesNextTo(UnsupportedInitializer::class.java, "hu.bme.mit.theta.frontend"))
        .filter {
          (ForeignExpr::class.java.isAssignableFrom(it) ||
            ForeignLitExpr::class.java.isAssignableFrom(it)) && it.concrete()
        }
    assertTrue(foreign.size >= 2, "found only $foreign")
    assertEquals(
      emptyList<Class<*>>(),
      foreign.filter { runCatching { XcfaSerialization.tableClasses.of(it) }.isFailure },
    )
  }

  @Test
  fun everyListedNameIsThatOfItsClass() {
    val names = XcfaSerialization.tableClasses.names.toList()
    assertEquals(names, XcfaSerialization.tableClasses.all.map { it.cls.name })
  }

  @Test
  fun everyCTypeIsWrittenOnceAndReferredTo() {
    val ctypes = concreteSealedSubclasses(CComplexType::class)
    assertTrue(ctypes.size > 20, "found only ${ctypes.size} C type classes")
    val definitions =
      ctypes.associateWith {
        runCatching { FrontendTableClasses.of(it.java).serializer }.getOrNull()
      }
    assertEquals(emptyList<KClass<*>>(), definitions.filterValues { it == null }.keys.toList())

    // A property naming a C type must write a reference: an inline one would be a separate copy.
    val inline = HashSet(ctypes.map { it.java.name } + CComplexType::class.java.name)
    val problems = ArrayList<String>()
    fun scan(owner: String, d: SerialDescriptor, seen: MutableSet<String>) {
      if (!seen.add(d.serialName)) return
      for (i in 0 until d.elementsCount) {
        val element = d.getElementDescriptor(i)
        if (element.serialName.removeSuffix("?") in inline) {
          problems.add("$owner.${d.getElementName(i)} writes a C type inline")
        } else {
          scan(owner, element, seen)
        }
      }
    }
    definitions.forEach { (cls, serializer) ->
      scan(cls.simpleName!!, serializer!!.descriptor, HashSet())
    }
    scan("LaidOutValue", LaidOutValue.serializer().descriptor, HashSet())
    assertTrue(problems.isEmpty(), problems.joinToString("\n"))

    // LayoutAttributesSerializer writes exactly these.
    assertEquals(
      listOf("packed", "alignedToBits"),
      ObjectLayout.Attributes::class.java.recordComponents.map { it.name },
    )
  }

  private fun concreteSealedSubclasses(root: KClass<*>): List<KClass<*>> =
    root.sealedSubclasses
      .flatMap { if (it.isSealed) concreteSealedSubclasses(it) else listOf(it) }
      .distinct()

  @Test
  fun parseContextAndXcfaFieldsAreCovered() {
    fun fields(c: Class<*>) =
      c.declaredFields.filter { !Modifier.isStatic(it.modifiers) }.map { it.name }.toSet()
    // What the serializer leaves out must be parse-time state (or the separately carried metadata).
    val serialized = ParseContext.serializer().descriptor.elementNames.toSet() + "traits"
    assertEquals(
      setOf(
        "metadata",
        "cStmtCounter",
        "accessedMembers",
        "everyMemberAccessed",
        "functionReturnTypes",
        "functionPointerVariables",
        "definedStructs",
        "incompleteStructDependents",
      ),
      fields(ParseContext::class.java) - serialized,
    )
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
