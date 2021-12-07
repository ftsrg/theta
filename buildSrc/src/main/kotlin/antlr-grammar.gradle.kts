import java.nio.file.Files

apply<AntlrPlugin>()

dependencies {
    val antlr: Configuration by configurations
    val implementation: Configuration by configurations

    antlr(Deps.Antlr.antlr)
    implementation(Deps.Antlr.runtime)
}

open class GenerateGrammarExtension(project: Project) {
    var packageName: String = "hu.bme.mit.${project.name.replace("-",".")}.dsl.gen"
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
