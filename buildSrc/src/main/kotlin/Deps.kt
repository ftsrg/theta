object Deps {
    val guava = "com.google.guava:guava:${Versions.guava}"

    object Antlr {
        val antlr = "org.antlr:antlr4:${Versions.antlr}"
        val runtime = "org.antlr:antlr4-runtime:${Versions.antlr}"
    }

    val z3 = "lib/com.microsoft.z3.jar"

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

    val delta = "lib/hu.bme.mit.delta"
    val deltaCollections = "lib/hu.bme.mit.delta.collections:${Versions.deltaCollections}"

    val koloboke = "com.koloboke:koloboke-api-jdk8:${Versions.koloboke}"

    val junit4 = "junit:junit:${Versions.junit}"

    object Mockito {
        val core = "org.mockito:mockito-core:${Versions.mockito}"
    }
}