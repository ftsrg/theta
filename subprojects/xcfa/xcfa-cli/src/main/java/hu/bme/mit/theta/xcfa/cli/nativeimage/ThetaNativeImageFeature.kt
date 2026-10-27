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
package hu.bme.mit.theta.xcfa.cli.nativeimage

import hu.bme.mit.theta.xcfa.cli.XcfaCli
import java.lang.reflect.Field
import java.lang.reflect.ParameterizedType
import java.nio.file.Files
import java.nio.file.Path
import java.util.zip.ZipFile
import kotlin.io.path.extension
import kotlin.io.path.invariantSeparatorsPathString
import kotlin.io.path.isDirectory
import kotlin.io.path.relativeTo
import org.graalvm.nativeimage.hosted.Feature
import org.graalvm.nativeimage.hosted.RuntimeJNIAccess
import org.graalvm.nativeimage.hosted.RuntimeReflection

/**
 * What the native image keeps for reflection and JNI, by rule rather than by recording a run.
 * - JCommander reads the options off the fields of [XcfaCli] and of the classes in `params`, so
 *   each of those is kept whole, with the enums its options take and every JCommander converter and
 *   validator. A new option is covered without touching this.
 * - The solvers' native code calls back into their Java bindings (callbacks, result objects), so
 *   the binding classes in [JNI_BINDINGS] are kept whole for JNI.
 *
 * native-image runs this at build time (it is named in `META-INF/native-image/.../native-image
 * .properties`); the JVM never loads it.
 */
class ThetaNativeImageFeature : Feature {

  private companion object {
    /** Packages (ending in `/`) or class name prefixes whose classes native libraries call into. */
    val JNI_BINDINGS =
      listOf(
        "com/microsoft/z3/Native",
        "com/microsoft/z3legacy/Native",
        "org/kframework/mpfr/",
        "org/sosy_lab/java_smt/solvers/mathsat5/Mathsat5NativeApi",
        "org/sosy_lab/java_smt/solvers/bitwuzla/api/",
        "org/sosy_lab/java_smt/solvers/opensmt/api/",
        "io/github/cvc5/",
        "io/github/cvc5/modes/",
      )
  }

  override fun beforeAnalysis(access: Feature.BeforeAnalysisAccess) {
    val classPath = access.applicationClassPath
    val options =
      classesIn(access, classPath, "hu/bme/mit/theta/xcfa/cli/params/") + XcfaCli::class.java
    options.forEach(::registerWhole)
    options
      .flatMap { it.declaredFields.toList() }
      .flatMap(::optionTypes)
      .filter { it.isEnum }
      .forEach(::registerWhole)
    for (pkg in listOf("com/beust/jcommander/converters/", "com/beust/jcommander/validators/")) {
      classesIn(access, classPath, pkg).forEach {
        RuntimeReflection.register(it)
        RuntimeReflection.register(*it.declaredConstructors)
      }
    }
    JNI_BINDINGS.flatMap { classesIn(access, classPath, it) }
      .forEach {
        RuntimeJNIAccess.register(it)
        RuntimeJNIAccess.register(*it.declaredFields)
        RuntimeJNIAccess.register(*it.declaredMethods)
        RuntimeJNIAccess.register(*it.declaredConstructors)
      }
  }

  private fun registerWhole(cls: Class<*>) {
    RuntimeReflection.register(cls)
    RuntimeReflection.register(*cls.declaredFields)
    RuntimeReflection.register(*cls.declaredMethods)
    RuntimeReflection.register(*cls.declaredConstructors)
  }

  /** The type of [field] and, for a collection of options, its element types. */
  private fun optionTypes(field: Field): List<Class<*>> =
    listOf(field.type) +
      ((field.genericType as? ParameterizedType)?.actualTypeArguments?.filterIsInstance<Class<*>>()
        ?: emptyList())

  /**
   * The classes on [classPath] whose names start with [prefix] (a package path ending in `/`, or a
   * class name prefix within one), nested ones too, but not those of subpackages.
   */
  private fun classesIn(
    access: Feature.BeforeAnalysisAccess,
    classPath: List<Path>,
    prefix: String,
  ): List<Class<*>> =
    classPath
      .flatMap { entry ->
        if (entry.isDirectory()) {
          Files.walk(entry).use { files ->
            files
              .filter { it.extension == "class" }
              .map { it.relativeTo(entry).invariantSeparatorsPathString }
              .toList()
          }
        } else if (entry.extension == "jar") {
          ZipFile(entry.toFile()).use { jar -> jar.entries().toList().map { it.name } }
        } else {
          emptyList()
        }
      }
      .filter { it.startsWith(prefix) && it.endsWith(".class") && '/' !in it.removePrefix(prefix) }
      .mapNotNull { access.findClassByName(it.removeSuffix(".class").replace('/', '.')) }
      .distinct()
}
