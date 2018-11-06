apply(plugin = "tool-common")

dependencies {
    val implementation: Configuration by configurations

    implementation(Deps.jcommander)
}

