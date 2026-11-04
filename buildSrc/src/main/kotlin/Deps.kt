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

import java.util.Locale

private fun getOs(): String {
    val os: String = System.getProperty("os.name")

    return when {
        os.lowercase(Locale.getDefault()).startsWith("linux") -> "linux"
        os.lowercase(Locale.getDefault()).startsWith("windows") -> "windows"
        os.lowercase(Locale.getDefault()).contains("mac") || os.lowercase(Locale.getDefault()).contains("darwin") -> "macos"
        else -> error("Operating system \"$os\" not supported.")
    }
}

object Deps {

    val guava = "com.google.guava:guava:${Versions.guava}"

    object Antlr {

        val antlr = "org.antlr:antlr4:${Versions.antlr}"
        val runtime = "org.antlr:antlr4-runtime:${Versions.antlr}"
    }

    val mpfr_java = when(getOs()) {
        "windows" -> listOf("lib/mpfr_java-1.4.jar", "lib/mpfr_java-1.0-windows64.jar") // version mismatch, best-effort
        "linux" -> listOf("lib/mpfr_java-1.4.jar", "lib/mpfr_java-1.4-linux64.jar")
        "macos" -> listOf("lib/mpfr_java-1.4.jar", "lib/mpfr_java-1.4-osx64.jar")
        else -> error("Operating system not supported")
    }

    const val z3Version = "5.3.3"
    val z3 = "com.microsoft:z3:$z3Version" // from the GitHub release, see mirrors.gradle.kts
    val z3Natives = setOf("libz3.dll", "libz3.dylib", "libz3.so", "libz3java.dll", "libz3java.dylib", "libz3java.so")
    // Release assets carrying the natives, per architecture. Platforms without a jar only have a zip.
    val z3NativeAssets = mapOf(
        "x64" to listOf("linux-x64.jar", "win-x64.jar", "x64-osx-13.3.zip"),
        "arm64" to listOf("arm64-glibc-2.38.zip", "osx-arm64.jar", "arm64-win.zip"),
    )
    val z3legacy = "lib/com.microsoft.z3legacy.jar"

    val javasmt = "org.sosy-lab:java-smt:6.0.0-499-gf35a21a8e" // hardcoded because deps also hardcoded
    val javasmtDeps = mapOf(
        "de.uni-freiburg.informatik.ultimate:smtinterpol:2.5-1242-g5c50fb6d" to setOf(), // no deps
        "io.github.uuverifiers:princess_2.13:2025-11-17" to setOf(), // no deps
        "io.github.uuverifiers:ostrich_2.13:2.0" to setOf(), // no deps
        "org.sosy-lab:javasmt-solver-mathsat:5.6.15" to setOf("libmathsat5j.so", "mathsat5j.dll", "mathsat.dll", "gmp.dll"),
        "org.sosy-lab:javasmt-solver-opensmt:2.9.2-ge4c80308" to setOf("libopensmtj.so"),
        "org.sosy-lab:javasmt-solver-cvc4:1.8-prerelease-2020-06-24-g7825d8f28:CVC4" to setOf("libcvc4.so", "libcvc4jni.so", "libcvc4parser.so"),
        "org.sosy-lab:javasmt-solver-cvc5:2026-02-26-d22638a" to setOf("libcvc5jni.dll", "libcvc5jni.dylib", "libcvc5jni.so"),
        "org.sosy-lab:javasmt-solver-bitwuzla:0.9.0-gd13ef925" to setOf("libbitwuzlaj.dll", "libbitwuzlaj.so"),
        "org.sosy-lab:javasmt-yices2:6.0.0-141-g04134287c" to setOf(), // no deps
        "org.sosy-lab:javasmt-solver-yices2:2.7.0-gdc5687ca" to setOf("libyices2java.so", "yices2java.dll")
    )
    val eldarica = "io.github.uuverifiers:eldarica_2.13:${Versions.eldarica}"

    val jcommander = "org.jcommander:jcommander:${Versions.jcommander}"

    val pnmlCore = "fr.lip6.pnml:fr.lip6.pnml.framework.coremodel:${Versions.pnmlFramework}"
    val pnmlPtnet = "fr.lip6.pnml:fr.lip6.pnml.framework.ptnet:${Versions.pnmlFramework}"
    val pnmlSymmetric = "fr.lip6.pnml:fr.lip6.pnml.framework.symmetricnet:${Versions.pnmlFramework}"
    val pnmlHlpn = "fr.lip6.pnml:fr.lip6.pnml.framework.hlpn:${Versions.pnmlFramework}"
    val pnmlPthlpng = "fr.lip6.pnml:fr.lip6.pnml.framework.pthlpng:${Versions.pnmlFramework}"
    val pnmlUtils = "fr.lip6.pnml:fr.lip6.pnml.framework.utils:${Versions.pnmlFramework}"
    val pnmlNupn = "fr.lip6.pnml:fr.lip6.pnml.nupn.toolinfo:${Versions.pnmlFramework}"

    val emfCommon = "org.eclipse.emf:org.eclipse.emf.common:${Versions.emfCommon}"
    val emfCodegen = "org.eclipse.emf:org.eclipse.emf.codegen:${Versions.emfCodegen}"
    val emfCodegenEcore = "org.eclipse.emf:org.eclipse.emf.codegen.ecore:${Versions.emfCodegenEcore}"
    val emfEcore = "org.eclipse.emf:org.eclipse.emf.ecore:${Versions.emfEcore}"
    val emfEcoreXmi = "org.eclipse.emf:org.eclipse.emf.ecore.xmi:${Versions.emfEcore}"

    val axiomApi = "org.apache.ws.commons.axiom:axiom-api:${Versions.axiom}"
    val axiomImpl = "org.apache.ws.commons.axiom:axiom-impl:${Versions.axiom}"
    val jing = "org.relaxng:jing:${Versions.jing}"

    val delta = "lib/hu.bme.mit.delta-0.0.1-all.jar"

    val hoaf = "lib/jhoafparser-1.1.1.jar"

    val junit5 = "org.junit.jupiter:junit-jupiter-api:${Versions.junit}"
    val junit5param = "org.junit.jupiter:junit-jupiter-params:${Versions.junit}"
    val junit5engine = "org.junit.jupiter:junit-jupiter-engine:${Versions.junit}"

    object Mockito {

        val core = "org.mockito:mockito-core:${Versions.mockito}"
        val extension = "org.mockito:mockito-junit-jupiter:${Versions.mockito}"
        val kotlin = "org.mockito.kotlin:mockito-kotlin:${Versions.mockitoKotlin}"
    }

    object Kotlin {

        val stdlib = "org.jetbrains.kotlin:kotlin-stdlib-jdk8:${Versions.kotlin}"
        val reflect = "org.jetbrains.kotlin:kotlin-reflect:${Versions.kotlin}"
    }

    val clikt = "com.github.ajalt.clikt:clikt:${Versions.clikt}"

    val kaml = "com.charleskorn.kaml:kaml:${Versions.kaml}"

    val kotlinxSerializationJson =
        "org.jetbrains.kotlinx:kotlinx-serialization-json:${Versions.kotlinxSerializationJson}"

    val nuprocess = "com.zaxxer:nuprocess:${Versions.nuprocess}"

    val hawtjni = "org.fusesource.hawtjni:hawtjni-runtime:${Versions.hawtjni}"
    val fastutil = "it.unimi.dsi:fastutil:${Versions.fastutil}"
}
