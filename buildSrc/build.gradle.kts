import java.io.FileOutputStream
import org.jetbrains.kotlin.gradle.plugin.KotlinSourceSet
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    `java-gradle-plugin`
    `kotlin-dsl`
    `kotlin-dsl-precompiled-script-plugins`
}

repositories {
    gradlePluginPortal()
}

apply(from = rootDir.resolve("../gradle/shared-with-buildSrc/mirrors.gradle.kts"))

kotlinDslPluginOptions {
    experimentalWarning.set(false)
}

val kotlinVersion: String by project
val shadowVersion: String by project

// https://github.com/gradle/kotlin-dsl/issues/430#issuecomment-414768887
fun gradlePlugin(id: String, version: String): String = "$id:$id.gradle.plugin:$version"

dependencies {
    compileOnly(gradleKotlinDsl())
    compile(kotlin("gradle-plugin", kotlinVersion))
    compile(gradlePlugin("com.github.johnrengelman.shadow", shadowVersion))
}

// Force the embeddable Kotlin compiler version to be the selected kotlinVersion.
// https://github.com/gradle/kotlin-dsl/issues/1207
configurations.all {
    val isKotlinCompiler = name == "embeddedKotlin" || name.startsWith("kotlin") || name.startsWith("kapt")
    if (!isKotlinCompiler) {
        resolutionStrategy.eachDependency {
            if (requested.group == "org.jetbrains.kotlin" && requested.module.name == "kotlin-compiler-embeddable") {
                useVersion(kotlinVersion)
            }
        }
    }
}

val versionsClassName = "Versions"
val generatedVersionsKotlinSrcDir = buildDir.resolve("generated-sources/versions/kotlin")
val generatedVersionsFile = generatedVersionsKotlinSrcDir.resolve("$versionsClassName.kt")

sourceSets {
    named("main") {
        withConvention(KotlinSourceSet::class) {
            kotlin.srcDir(generatedVersionsKotlinSrcDir)
        }
    }
}

fun generateVersionsSource(): String {
    val text = StringBuilder()

    text.appendln("object $versionsClassName {")

    for (property in project.properties) {
        if (property.key.endsWith("Version")) {
            val keyWithoutVersion = property.key.substringBefore("Version")
            text.appendln("   const val `$keyWithoutVersion` = \"${property.value}\"")
        }
    }

    text.appendln("}")

    return text.toString()
}

tasks {
    val generateVersions by creating {
        description = "Updates Versions.kt from project properties."
        group = "build"
        outputs.dirs(generatedVersionsKotlinSrcDir)

        doLast {
            val versionsSource = generateVersionsSource()
            generatedVersionsKotlinSrcDir.mkdirs()
            generatedVersionsFile.writeText(versionsSource)
        }
    }

    named("compileKotlin", KotlinCompile::class) {
        dependsOn(generateVersions)
    }
}
