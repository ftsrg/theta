/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

    val z3 = "lib/com.microsoft.z3.jar"
    val z3legacy = "lib/com.microsoft.z3legacy.jar"

    val cvc5 = "lib/cvc5.jar"

    val javasmt = "org.sosy-lab:java-smt:${Versions.javasmt}"
    val javasmtLocal = "lib/javasmt.jar"
    val sosylabCommon = "org.sosy-lab:common:${Versions.sosylab}"

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
    val logback = "ch.qos.logback:logback-classic:${Versions.logback}"

    val delta = "delta:hu.bme.mit.delta:${Versions.delta}"
    val deltaCollections = "delta:hu.bme.mit.delta.collections:${Versions.deltaCollections}"

    val koloboke = "com.koloboke:koloboke-api-jdk8:${Versions.koloboke}"

    val junit4 = "junit:junit:${Versions.junit}"

    object Mockito {

        val core = "org.mockito:mockito-core:${Versions.mockito}"
    }
}