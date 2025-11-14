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
import org.gradle.api.Plugin
import org.gradle.api.Project
import org.gradle.api.plugins.JavaApplication
import org.gradle.api.tasks.SourceSetContainer
import java.io.File
import java.util.jar.JarFile
import java.util.jar.JarOutputStream

/**
 * Creates a WSL-compatible jar file that can be executed in Windows Subsystem for Linux (WSL).
 * The plugin sets the class path in the jar manifest to use WSL-style relative paths.
 *
 * Use-case: run gradle build on Windows, then run the resulting WSL jar in WSL without rebuilding.
 */
class WslJarPlugin : Plugin<Project> {
  override fun apply(project: Project) {
    if (!System.getProperty("os.name").lowercase().contains("windows")) return

    if (!project.plugins.hasPlugin("application")) {
      throw IllegalStateException(
        "WslJarPlugin requires the 'application' plugin to be applied."
      )
    }
    val application = project.extensions.getByType(JavaApplication::class.java)
    val sourceSets = project.extensions.getByName("sourceSets") as SourceSetContainer

    project.tasks.register("wslJar") {
      dependsOn(project.tasks.named("jar"))

      doLast {
        check(System.getProperty("os.name").lowercase().contains("windows")) {
          "The WSL jar can only be created on Windows hosts."
        }
        val wslPath: File.() -> String = {
          absolutePath.let {
            val drive = it[0].lowercase()
            "/mnt/$drive${it.substring(2).replace("\\", "/")}"
          }
        }
        val relativePath: String.(String) -> String = { base ->
          val thisSplit = this.split("/").filter { it.isNotEmpty() }
          val baseSplit = base.split("/").filter { it.isNotEmpty() }
          val commonLength = thisSplit.zip(baseSplit).takeWhile { it.first == it.second }.count()
          val upLevels = baseSplit.size - commonLength
          val downLevels = thisSplit.drop(commonLength)
          buildString {
            repeat(upLevels) { append("../") }
            append(downLevels.joinToString("/"))
          }
        }

        val artifactDir = project.layout.buildDirectory.dir("libs").get().asFile
        val artifactPath = artifactDir.wslPath()
        val artifact = File(artifactDir, "${project.name}-${project.version}.jar")
        JarFile(artifact).use { jar ->
          val manifest = jar.manifest
          val attrs = manifest.mainAttributes
          attrs.putValue("Main-Class", application.mainClass.get())
          val classPath = sourceSets.getByName("main").runtimeClasspath.files.joinToString(" ") { f ->
            f.wslPath().relativePath(artifactPath)
          }
          attrs.putValue("Class-Path", classPath)

          val wslJar = File(artifact.parentFile, "${project.name}-${project.version}-wsl.jar")
          JarOutputStream(wslJar.outputStream(), manifest).use { jos ->
            jar.entries().asSequence().forEach { entry ->
              if (!entry.name.equals("META-INF/MANIFEST.MF", ignoreCase = true)) {
                jos.putNextEntry(entry)
                jar.getInputStream(entry).use { input ->
                  input.copyTo(jos)
                }
                jos.closeEntry()
              }
            }
          }
        }
      }
    }
  }
}