import java.util.Locale
import java.util.Locale.getDefault

/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
plugins {
    `java-library`
    `maven-publish`
    signing
}

open class MavenArtifactExtension(project: Project) {

  private val capitalize: ((String) -> CharSequence) = {
    it.replaceFirstChar {
      if (it.isLowerCase()) it.titlecase(
        getDefault()
      ) else it.toString()
    }
  }
  var artifactId: String = project.name
    var name: String = project.name.split("-").joinToString(" ", transform = capitalize)
    var description: String = project.name.split("-").let {
        it.subList(1, it.size).joinToString(" ", transform = capitalize)
    } + " subproject in the Theta model checking framework"
    var url: String = "https://theta.mit.bme.hu/"
    var licenseName: String = "The Apache License, Version 2.0"
    var licenseUrl: String = "http://www.apache.org/licenses/LICENSE-2.0.txt"
    var connection: String = "scm:git:git://github.com/ftsrg/theta.git"
    var developerConnection: String = "scm:git:ssh://github.com:ftsrg/theta.git"
}

val artifactConfig = extensions.create<MavenArtifactExtension>("maven-artifact", project)

val javadocJar by tasks.registering(Jar::class) {
    archiveClassifier.set("javadoc")
    from(tasks.withType(Javadoc::class.java).getByName("javadoc"))
}

val sourcesJar by tasks.registering(Jar::class) {
    archiveClassifier.set("sources")
    from(sourceSets.main.get().allSource)
}

// Check if "antlr-common" plugin is applied and if the "generateGrammarSource" task is available
// If yes, add a task dependency from "sourcesJar" to "generateGrammarSource"
project.plugins.withType<AntlrPlugin> {
    tasks.findByName("generateGrammarSource")?.let { genTask ->
        tasks.named("sourcesJar") { dependsOn(genTask) }
    }
}

publishing {
    publications {
        create<MavenPublication>("mavenJava") {
            artifactId = artifactConfig.artifactId
            from(components["java"])
            artifact(sourcesJar)
            artifact(javadocJar)
            versionMapping {
                usage("java-api") { fromResolutionOf("runtimeClasspath") }
                usage("java-runtime") { fromResolutionResult() }
            }
            pom {
                name.set(artifactConfig.name)
                description.set(artifactConfig.description)
                url.set(artifactConfig.url)
                licenses {
                    license {
                        name.set(artifactConfig.licenseName)
                        url.set(artifactConfig.licenseUrl)
                    }
                }
                developers {
                    val contribFile = project.rootProject.rootDir.toPath().resolve("CONTRIBUTORS.md").toFile()
                    if (contribFile.exists()) {
                        contribFile.readLines().forEach { line ->
                            "\\* \\[([^]]+)]\\(([^)]+)\\)".toRegex().matchEntire(line)?.let { m ->
                                val (parsedName, parsedUrl) = m.destructured
                                developer {
                                    name.set(parsedName)
                                    url.set(parsedUrl)
                                }
                            }
                        }
                    }
                }
                scm {
                    connection.set(artifactConfig.connection)
                    developerConnection.set(artifactConfig.developerConnection)
                    url.set(artifactConfig.url)
                }
            }
        }
    }
    repositories {
        maven {
            name = "OSSRH"
            val releasesRepoUrl = uri("https://s01.oss.sonatype.org/service/local/staging/deploy/maven2/")
            val snapshotsRepoUrl = uri("https://s01.oss.sonatype.org/content/repositories/snapshots/")
            url = if (version.toString().endsWith("SNAPSHOT")) snapshotsRepoUrl else releasesRepoUrl
            credentials {
                // Support both username/password and token-based credentials
                username = System.getenv("OSSRH_USERNAME") ?: System.getenv("OSSRH_TOKEN_USERNAME")
                password = System.getenv("OSSRH_PASSWORD") ?: System.getenv("OSSRH_TOKEN_PASSWORD")
            }
        }
    }
}

signing {
    // Prefer Gradle properties if provided; fallback to environment variables
    val key = (project.findProperty("signingKey") as String?) ?: System.getenv("PGP_KEY")
    val pwd = (project.findProperty("signingPassword") as String?) ?: System.getenv("PGP_PWD")
    if (!key.isNullOrBlank() && !pwd.isNullOrBlank()) {
        useInMemoryPgpKeys(key, pwd)
        sign(publishing.publications)
    } else {
        // logger.warn("Signing keys not provided; publications will not be signed.")
    }
}

tasks.javadoc {
    if (JavaVersion.current().isJava9Compatible) {
        (options as StandardJavadocDocletOptions).addBooleanOption("html5", true)
    }
}