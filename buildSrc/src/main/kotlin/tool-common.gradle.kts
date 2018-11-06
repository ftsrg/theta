import com.github.jengelman.gradle.plugins.shadow.ShadowPlugin

apply<ApplicationPlugin>()
apply<ShadowPlugin>()

tasks {
    val libPath: String by rootProject.extra
    val execPath: String by rootProject.extra

    fun JavaExec.setupEnvironment() {
        environment["PATH"] = execPath
        environment["LD_LIBRARY_PATH"] = libPath
    }

    named("run", JavaExec::class).configure { setupEnvironment() }
    named("runShadow", JavaExec::class).configure { setupEnvironment() }
}
