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

import java.nio.file.Files
import java.nio.file.StandardOpenOption
import org.gradle.api.DefaultTask
import org.gradle.api.tasks.CacheableTask
import org.gradle.api.tasks.Input
import org.gradle.api.tasks.OutputDirectory
import org.gradle.api.tasks.TaskAction
import org.gradle.api.provider.Property
import org.gradle.api.file.DirectoryProperty

@CacheableTask
abstract class ComputeReleaseInfoTask : DefaultTask() {
    @get:Input
    abstract val version: Property<String>

    @get:Input
    abstract val releaseMessage: Property<String>

    @get:OutputDirectory
    abstract val outputDir: DirectoryProperty

    private fun runGit(vararg args: String): String {
        return try {
            val process = ProcessBuilder("git", *args)
                .redirectOutput(ProcessBuilder.Redirect.PIPE)
                .redirectError(ProcessBuilder.Redirect.PIPE)
                .start()
            val output = process.inputStream.bufferedReader().readText().trim()
            process.waitFor()
            output
        } catch (_: Exception) {
            ""
        }
    }

    @TaskAction
    fun generate() {
        val versionStr = version.get()
        val lastTag = runGit("describe", "--abbrev=0", "--tags")
        val diffFiles = runGit("diff", lastTag, "--name-only")
        val subprojects = diffFiles
            .lineSequence()
            .filter { it.startsWith("subprojects/") }
            .map { it.split('/') }
            .filter { it.size >= 3 }
            .map { it[1] + "/" + it[2] }
            .distinct()
            .sorted()
            .joinToString("\n")
        val messageInput = releaseMessage.getOrElse("")
        val message = buildString {
            append(messageInput)
            if (messageInput.isNotEmpty()) append('\n')
            append('\n')
            append("Modified subprojects (since $lastTag):\n")
            append(subprojects)
        }

        val outDir = outputDir.get().asFile
        outDir.mkdirs()
        Files.writeString(outDir.toPath().resolve("version.txt"), versionStr, StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING)
        Files.writeString(outDir.toPath().resolve("tagname.txt"), "v$versionStr", StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING)
        Files.writeString(outDir.toPath().resolve("message.txt"), message, StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING)

        logger.lifecycle("Release info written to ${outDir.absolutePath}")
    }
}

val computeReleaseInfo by tasks.registering(ComputeReleaseInfoTask::class) {
    group = "release"
    description = "Compute release info: version, tagname, and message with modified subprojects"

    version.set(providers.provider { project.version.toString() })
    releaseMessage.set(providers.environmentVariable("RELEASE_MESSAGE").orElse(""))
    outputDir.set(project.layout.buildDirectory.dir("release-info"))
}
