plugins {
    `java-library`
    `maven-publish`
    signing
}


open class MavenArtifactExtension(project: Project) {
    var artifactId: String = project.name
    var name: String = project.name.split("-").joinToString(" ", transform = String::capitalize)
    var description: String = project.name.split("-").let{ it.subList(1, it.size).joinToString(" ", transform = String::capitalize) } + " subproject in the Theta model checking framework"
    var url: String = "https://theta.mit.bme.hu/"
    var licenseName: String = "The Apache License, Version 2.0"
    var licenseUrl: String = "http://www.apache.org/licenses/LICENSE-2.0.txt"
    var connection: String = "scm:git:git://github.com/ftsrg/theta.git"
    var developerConnection: String = "scm:git:ssh://github.com:ftsrg/theta.git"
}

val artifactConfig = extensions.create<MavenArtifactExtension>("maven-artifact", project)

java {
    withJavadocJar()
    withSourcesJar()
}
tasks {
    publishing {
        publications {
            create<MavenPublication>("mavenJava") {
                artifactId = artifactConfig.artifactId
                from(components["java"])
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
                        val contribFile = project.rootProject.rootDir.toPath().resolve("CONTRIBUTORS.md").toFile()
                        if (contribFile.exists()) {
                            contribFile.readLines().forEach { line ->
                                "\\* \\[(.*)]\\((.*)\\)".toRegex().matchEntire(line)?.let { matchResult ->
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
                val releasesRepoUrl = uri("${project.gradle.gradleUserHomeDir}/.m2/releases")
                val snapshotsRepoUrl = uri("${project.gradle.gradleUserHomeDir}/.m2/snapshots")
                url = if (version.toString().endsWith("SNAPSHOT")) snapshotsRepoUrl else releasesRepoUrl
                print(url)
            }
        }
    }
}

signing {
    sign(publishing.publications["mavenJava"])
}

tasks.javadoc {
    if (JavaVersion.current().isJava9Compatible) {
        (options as StandardJavadocDocletOptions).addBooleanOption("html5", true)
    }
}