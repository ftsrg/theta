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

object Deps {

    val guava = "com.google.guava:guava:${Versions.guava}"
    val gson = "com.google.code.gson:gson:${Versions.gson}"

    object Antlr {

        val antlr = "org.antlr:antlr4:${Versions.antlr}"
        val runtime = "org.antlr:antlr4-runtime:${Versions.antlr}"
    }

    val z3 = "org.sosy-lab:javasmt-solver-z3:4.14.0"
    val z3legacy = "lib/com.microsoft.z3legacy.jar"

    val javasmt = "org.sosy-lab:java-smt:5.0.1-523-g9001c0ea4" // hardcoded because deps also hardcoded
    val javasmtDeps = listOf(
        "org.sosy-lab:javasmt-solver-mathsat5:5.6.11-sosy1",
        z3,
        "org.sosy-lab:javasmt-solver-opensmt:2.9.0-gef441e1c",
        "org.sosy-lab:javasmt-solver-cvc4:1.8-prerelease-2020-06-24-g7825d8f28:CVC4",
        "org.sosy-lab:javasmt-solver-cvc5:1.2.1-g8594a8e4dc",
        "org.sosy-lab:javasmt-solver-bitwuzla:0.7.0-13.1-g595512ae",
        "org.sosy-lab:javasmt-yices2:4.1.1-734-g3732f7e08"
    )

    val jcommander = "com.beust:jcommander:${Versions.jcommander}"

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
    val jing = "com.thaiopensource:jing:${Versions.jing}"

    val delta = "lib/hu.bme.mit.delta"
    val deltaCollections = "lib/hu.bme.mit.delta.collections:${Versions.deltaCollections}"

    val koloboke = "com.koloboke:koloboke-api-jdk8:${Versions.koloboke}"

    val junit4 = "junit:junit:${Versions.junit4}"
    val junit4engine = "org.junit.vintage:junit-vintage-engine"
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

    val nuprocess = "com.zaxxer:nuprocess:${Versions.nuprocess}"
}
