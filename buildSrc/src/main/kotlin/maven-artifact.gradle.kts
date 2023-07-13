/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

    var artifactId: String = project.name
    var name: String = project.name.split("-").joinToString(" ", transform = String::capitalize)
    var description: String = project.name.split("-").let {
        it.subList(1, it.size).joinToString(" ", transform = String::capitalize)
    } + " subproject in the Theta model checking framework"
    var url: String = "https://theta.mit.bme.hu/"
    var licenseName: String = "The Apache License, Version 2.0"
    var licenseUrl: String = "http://www.apache.org/licenses/LICENSE-2.0.txt"
    var connection: String = "scm:git:git://github.com/ftsrg/theta.git"
    var developerConnection: String = "scm:git:ssh://github.com:ftsrg/theta.git"
}

val artifactConfig = extensions.create<MavenArtifactExtension>("maven-artifact", project)

val javadocJar by tasks.creating(Jar::class) {
    archiveClassifier.set("javadoc")
    from(tasks.withType(Javadoc::class.java).getByName("javadoc"))
}

val sourcesJar by tasks.creating(Jar::class) {
    archiveClassifier.set("sources")
    from(sourceSets.main.get().allSource)
}

tasks {
    publishing {
        publications {
            create<MavenPublication>("mavenJava") {
                artifactId = artifactConfig.artifactId
                from(components["java"])
                artifact(sourcesJar)
                artifact(javadocJar)
                versionMapping {
                    usage("java-api") {
                        fromResolutionOf("runtimeClasspath")
                    }
                    usage("java-runtime") {
                        fromResolutionResult()
                    }
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
                        val contribFile = project.rootProject.rootDir.toPath()
                            .resolve("CONTRIBUTORS.md").toFile()
                        if (contribFile.exists()) {
                            contribFile.readLines().forEach { line ->
                                "\\* \\[(.*)]\\((.*)\\)".toRegex().matchEntire(line)
                                    ?.let { matchResult ->
                                        val (parsedName, parsedUrl) = matchResult.destructured
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
                val releasesRepoUrl = uri(
                    "https://s01.oss.sonatype.org/service/local/staging/deploy/maven2/")
                val snapshotsRepoUrl = uri(
                    "https://s01.oss.sonatype.org/content/repositories/snapshots/")
                url = if (version.toString()
                        .endsWith("SNAPSHOT")) snapshotsRepoUrl else releasesRepoUrl
                credentials {
                    username = System.getenv("OSSRH_USERNAME")
                    password = System.getenv("OSSRH_PASSWORD")
                }
            }
        }
    }
}

signing {
    val key = System.getenv("PGP_KEY")
    val pwd = System.getenv("PGP_PWD")
    useInMemoryPgpKeys(key, pwd)
    sign(publishing.publications["mavenJava"])
}

tasks.javadoc {
    if (JavaVersion.current().isJava9Compatible) {
        (options as StandardJavadocDocletOptions).addBooleanOption("html5", true)
    }
}