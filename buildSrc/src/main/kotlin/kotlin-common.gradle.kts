import org.jetbrains.kotlin.gradle.plugin.KotlinPlatformJvmPlugin
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile
apply(plugin = "java-common")
apply<KotlinPlatformJvmPlugin>()
dependencies {
    val implementation: Configuration by configurations
    implementation(Deps.Kotlin.stdlib)
}
tasks {
    withType<KotlinCompile>() {
        kotlinOptions {
            jvmTarget = "1.8"
        }
    }
}