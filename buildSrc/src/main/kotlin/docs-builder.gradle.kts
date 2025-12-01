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

open class DocsBuilderExtension {
    var sourceDir: String = "doc/wiki"
    var outputDir: String = "wiki"
    var requirementsFile: String? = null
}

val extension = extensions.create<DocsBuilderExtension>("docsBuilder")

val buildDocs by tasks.registering(Exec::class) {
    group = "documentation"
    description = "Build documentation using mkdocs"
    
    workingDir(rootProject.file(extension.sourceDir))
    
    commandLine("mkdocs", "build", "--site-dir", extension.outputDir)
    
    inputs.dir(rootProject.file(extension.sourceDir))
    outputs.dir(rootProject.file("${extension.sourceDir}/${extension.outputDir}"))
    
    doFirst {
        if (!commandExists("mkdocs")) {
            throw GradleException("mkdocs is not installed. Run 'pip install mkdocs mkdocs-material python-markdown-math mkdocs-awesome-pages-plugin' (or equivalent) manually.")
        }
    }
}

val cleanDocs by tasks.registering(Delete::class) {
    group = "documentation"
    description = "Clean built documentation"
    
    delete(rootProject.file("${extension.sourceDir}/${extension.outputDir}"))
}

tasks.named("clean") {
    dependsOn(cleanDocs)
}

fun commandExists(command: String): Boolean {
    return try {
        val process = ProcessBuilder("which", command)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start()
        process.waitFor()
        process.exitValue() == 0
    } catch (e: Exception) {
        false
    }
}
