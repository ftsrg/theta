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

    implementation(project(":theta-core"))
}