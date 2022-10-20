plugins {
    id("kotlin-common")
}

dependencies {
    implementation(project(":theta-common"))
    implementation(project(":theta-core"))
    implementation(project(":theta-grammar"))
    implementation(project(":theta-c-frontend"))
}
