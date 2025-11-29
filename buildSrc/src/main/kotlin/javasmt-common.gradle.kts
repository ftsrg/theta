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

import java.net.URI
import java.net.URL
import java.nio.file.Files
import java.security.MessageDigest

fun md5(file: File): String {
    val buffer = ByteArray(8192)
    val digest = MessageDigest.getInstance("MD5")
    file.inputStream().use { fis ->
        var read = fis.read(buffer)
        while (read != -1) {
            digest.update(buffer, 0, read)
            read = fis.read(buffer)
        }
    }
    return digest.digest().joinToString("") { "%02x".format(it) }
}

val archSuffix = when (val arch = System.getProperty("os.arch")) {
    "x86_64", "amd64" -> "x64"
    "aarch64" -> "arm64"
    else -> throw GradleException("Unsupported architecture: $arch")
}

tasks.register("downloadJavaSmtLibs") {
    val outputDir = rootProject.layout.projectDirectory.dir("lib")

    doLast {
        val extensions = listOf("so", "dll", "dylib")
        val baseUrl = "https://repo1.maven.org/maven2"

        outputDir.asFile.mkdirs()

        Deps.javasmtDeps.forEach { dep ->
            val (group, artifact, version) = dep.split(":")

            val path = group.replace('.', '/') + "/$artifact/$version"
            val artifactUrl = "$baseUrl/$path/"

            println("Fetching from: $artifactUrl")

            val html = URI.create(artifactUrl).toURL().readText()
            val regex = Regex("href=\"([^\"]*?-$archSuffix\\.(${extensions.joinToString("|")}))\"")

            var matches = regex.findAll(html).map { it.groupValues[1] }.toSet()

            if (matches.isEmpty()) {
                println("  No $archSuffix binaries found for $artifact:$version, retrying suffixless")
                val regex = Regex("href=\"([^\"]*?\\.(${extensions.joinToString("|")}))\"")

                matches = regex.findAll(html).map { it.groupValues[1] }.toSet()
                if(matches.isEmpty()) {
                    println("  No suffixless binaries found for $artifact:$version, giving up.")
                    return@forEach
                }
            }

            matches.forEach { fileName ->
                val fileUrl = URI.create("$artifactUrl$fileName").toURL()

                val md5url = URI.create("$artifactUrl$fileName.md5").toURL()

                // Strip prefix and -arch suffix
                val cleanName = fileName
                    .removePrefix("$artifact-$version-")
                    .replace("-$archSuffix", "")

                val targetFile = outputDir.asFile.resolve(cleanName)

                val md5 = md5url.openStream().readAllBytes().decodeToString()

                // Compare hash if file exists
                if (targetFile.exists()) {
                    val existingHash = md5(targetFile)
                    val newHash = md5
                    if (existingHash == newHash) {
                        println(" Skipping (same hash): $cleanName ($existingHash)")
                        return@forEach
                    } else {
                        println("  Overwriting (hash changed): $cleanName ($existingHash vs. $newHash)")
                    }
                } else {
                    println("  Downloading new: $cleanName ($md5)")
                }

                // Download to temp file
                val tmpFile = Files.createTempFile("download-", null).toFile()
                fileUrl.openStream().use { input ->
                    tmpFile.outputStream().use { output ->
                        input.copyTo(output)
                    }
                }

                tmpFile.copyTo(targetFile, overwrite = true)
                tmpFile.delete()
            }
        }

        println("Done. Libraries saved to: ${outputDir.asFile.absolutePath}")
    }
}