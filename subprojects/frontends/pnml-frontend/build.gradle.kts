plugins {
    id("java-common")
}

repositories {
    mavenLocal()
}

dependencies {
    implementation(Deps.pnmlCore)
    implementation(Deps.pnmlSymmetric)
    implementation(Deps.pnmlPtnet)
    implementation(Deps.pnmlUtils)
    implementation(Deps.pnmlHlpn)
    implementation(Deps.pnmlNupn)
    implementation(Deps.pnmlPthlpng)

    implementation(Deps.emfEcore)
    implementation(Deps.emfCodegenEcore)
    implementation(Deps.emfCodegen)
    implementation(Deps.emfEcoreXmi)
    implementation(Deps.emfCommon)

    implementation(Deps.axiomImpl)
    implementation(Deps.axiomApi)
    implementation(Deps.logback)
    implementation(Deps.jing)
    implementation(Deps.koloboke)

    implementation(Deps.delta)
    implementation(Deps.deltaCollections)

    implementation(Deps.jcommander)

    compile(project(":theta-core"))
}