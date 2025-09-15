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

apply<AntlrPlugin>()

dependencies {
    val antlr: Configuration by configurations
    val implementation: Configuration by configurations

    antlr(Deps.Antlr.antlr)
    implementation(Deps.Antlr.runtime)
}

open class GenerateGrammarExtension(project: Project) {

    var packageName: String = "hu.bme.mit.${project.name.replace("-", ".")}.dsl.gen"
}

tasks {
    val grammar = extensions.create<GenerateGrammarExtension>("grammar", project)

    named("generateGrammarSource", AntlrTask::class) {
        val packageName = grammar.packageName
        val directoryName = packageName.replace(".", File.separator)
        val pacakgeQualifiedOutputDirectory = outputDirectory.resolve(directoryName)
        outputDirectory = pacakgeQualifiedOutputDirectory

        arguments.addAll(listOf("-package", packageName, "-Werror", "-visitor"))
    }
}
