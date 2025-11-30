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

import java.time.LocalDate

val copyrightHeader = """/*
 *  Copyright %d Budapest University of Technology and Economics
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
"""

fun getLastModifiedYear(file: File): Int? {
    return try {
        val process = ProcessBuilder("git", "log", "-1", "--format=%ad", "--date=format:%Y", file.absolutePath)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start()
        process.waitFor()
        val yearStr = process.inputStream.bufferedReader().readText().trim()
        if (yearStr.isNotEmpty()) yearStr.toIntOrNull() else null
    } catch (e: Exception) {
        null
    }
}

fun extractCopyrightYear(file: File): Int? {
    val lines = file.readLines()
    if (lines.size < 2) return null
    val headerLine = lines[1]
    val yearRegex = Regex("""\d{4}""")
    return yearRegex.find(headerLine)?.value?.toIntOrNull()
}

fun hasCopyrightHeader(file: File): Boolean {
    val lines = file.readLines()
    if (lines.size < 2) return false
    return lines[1].contains("Budapest University of Technology")
}

tasks.register("checkCopyright") {
    group = "verification"
    description = "Check copyright headers in .java, .kt, and .kts files"

    doLast {
        val errors = mutableListOf<String>()
        val sourceFiles = fileTree(projectDir) {
            include("**/*.java", "**/*.kt", "**/*.kts")
            exclude("**/build/**", "**/bin/**", "**/.gradle/**")
        }

        sourceFiles.forEach { file ->
            val relativePath = file.relativeTo(rootDir)
            
            if (!hasCopyrightHeader(file)) {
                errors.add("$relativePath has no copyright header")
            } else {
                val headerYear = extractCopyrightYear(file)
                val lastModifiedYear = getLastModifiedYear(file) ?: LocalDate.now().year
                
                if (headerYear != null && headerYear != lastModifiedYear) {
                    errors.add("$relativePath has mismatched copyright year: should be $lastModifiedYear (instead of $headerYear)")
                }
            }
        }

        if (errors.isNotEmpty()) {
            errors.forEach { logger.error(it) }
            throw GradleException("Copyright check failed with ${errors.size} error(s)")
        } else {
            logger.lifecycle("Copyright check passed")
        }
    }
}

tasks.register("applyCopyright") {
    group = "formatting"
    description = "Apply or update copyright headers in .java, .kt, and .kts files"

    doLast {
        val sourceFiles = fileTree(projectDir) {
            include("**/*.java", "**/*.kt", "**/*.kts")
            exclude("**/build/**", "**/bin/**", "**/.gradle/**")
        }

        var updatedCount = 0
        var addedCount = 0

        sourceFiles.forEach { file ->
            val relativePath = file.relativeTo(rootDir)
            val lastModifiedYear = getLastModifiedYear(file) ?: LocalDate.now().year
            val newHeader = copyrightHeader.format(lastModifiedYear)

            val content = file.readText()
            val lines = file.readLines()

            if (!hasCopyrightHeader(file)) {
                // Add copyright header
                val newContent = newHeader + "\n" + content
                file.writeText(newContent)
                logger.lifecycle("Added copyright header to $relativePath")
                addedCount++
            } else {
                val headerYear = extractCopyrightYear(file)
                if (headerYear != null && headerYear != lastModifiedYear) {
                    // Update year in existing header
                    val updatedLines = lines.toMutableList()
                    updatedLines[1] = " *  Copyright $lastModifiedYear Budapest University of Technology and Economics"
                    file.writeText(updatedLines.joinToString("\n") + "\n")
                    logger.lifecycle("Updated copyright year in $relativePath from $headerYear to $lastModifiedYear")
                    updatedCount++
                }
            }
        }

        logger.lifecycle("Copyright application complete: $addedCount headers added, $updatedCount headers updated")
    }
}
