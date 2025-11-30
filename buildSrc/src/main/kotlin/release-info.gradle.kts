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

fun runGit(vararg args: String): String {
    return try {
        val process = ProcessBuilder("git", *args)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start()
        process.waitFor()
        process.inputStream.bufferedReader().readText().trim()
    } catch (e: Exception) {
        ""
    }
}

val computeReleaseInfo by tasks.registering {
    group = "release"
    description = "Compute release info: version, tagname, and message with modified subprojects"

    doLast {
        val versionStr = project.version.toString()
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
        val messageInput = System.getenv("RELEASE_MESSAGE") ?: ""
        val message = buildString {
            append(messageInput)
            if (messageInput.isNotEmpty()) append('\n')
            append('\n')
            append("Modified subprojects (since $lastTag):\n")
            append(subprojects)
        }

        val outDir = project.layout.buildDirectory.dir("release-info").get().asFile
        outDir.mkdirs()
        Files.writeString(outDir.toPath().resolve("version.txt"), versionStr, StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING)
        Files.writeString(outDir.toPath().resolve("tagname.txt"), "v$versionStr", StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING)
        Files.writeString(outDir.toPath().resolve("message.txt"), message, StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING)

        logger.lifecycle("Release info written to ${outDir.absolutePath}")
    }
}
