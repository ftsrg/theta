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

import org.gradle.api.provider.Property

abstract class DocsBuilderExtension {
    abstract val sourceDir: Property<String>
    abstract val outputDir: Property<String>
    abstract val requirementsFile: Property<String>
    
    init {
        sourceDir.convention("doc/wiki")
        outputDir.convention("wiki")
    }
}

val extension = extensions.create<DocsBuilderExtension>("docsBuilder")

val buildDocs by tasks.registering(Exec::class) {
    group = "documentation"
    description = "Build documentation using mkdocs"
    
    val sourceDirPath = extension.sourceDir.map { rootProject.file(it) }
    val outputDirValue = extension.outputDir
    
    // Use doFirst to set workingDir at execution time
    doFirst {
        workingDir = sourceDirPath.get()
        commandLine("mkdocs", "build", "--site-dir", outputDirValue.get())
        
        // Check if mkdocs is installed
        val commandExists = try {
            val process = ProcessBuilder("which", "mkdocs")
                .redirectOutput(ProcessBuilder.Redirect.PIPE)
                .redirectError(ProcessBuilder.Redirect.PIPE)
                .start()
            process.waitFor()
            process.exitValue() == 0
        } catch (e: Exception) {
            false
        }
        
        if (!commandExists) {
            throw GradleException("mkdocs is not installed. Run 'pip install mkdocs mkdocs-material python-markdown-math mkdocs-awesome-pages-plugin' (or equivalent) manually.")
        }
    }
    
    inputs.dir(sourceDirPath)
    outputs.dir(sourceDirPath.zip(outputDirValue) { source, output -> 
        source.resolve(output)
    })
}

val cleanDocs by tasks.registering(Delete::class) {
    group = "documentation"
    description = "Clean built documentation"
    
    val sourceDirPath = extension.sourceDir.map { rootProject.file(it) }
    val outputDirValue = extension.outputDir
    
    delete(sourceDirPath.zip(outputDirValue) { source, output -> 
        source.resolve(output)
    })
}

tasks.named("clean") {
    dependsOn(cleanDocs)
}
