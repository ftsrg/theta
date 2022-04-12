plugins {
    id("java-common")
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

    implementation(files(rootDir.resolve(Deps.delta)))
    implementation(files(rootDir.resolve(Deps.deltaCollections)))

    implementation(Deps.jcommander)

    compile(project(":theta-core"))
    compile(project(":theta-analysis"))
}