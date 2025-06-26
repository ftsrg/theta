package hu.bme.mit.theta.ksp

import com.google.devtools.ksp.getAllSuperTypes
import com.google.devtools.ksp.isAbstract
import com.google.devtools.ksp.processing.*
import com.google.devtools.ksp.symbol.*

class PolymorphicModuleProcessor(
    private val codeGenerator: CodeGenerator,
    private val logger: KSPLogger,
    private val pack: String,
    private val baseClass: String,
) : SymbolProcessor {

    override fun process(resolver: Resolver): List<KSAnnotated> {
        val topLevelClassFqn = "$pack.$baseClass"
        val generatedPack = "$pack.generated"

        val subclasses = resolver
            .getSymbolsWithAnnotation("kotlinx.serialization.Serializable")
            .filterIsInstance<KSClassDeclaration>()
            .filter { !it.isAbstract() && it.getSealedSubclasses().toList().isEmpty() }
            .filter {
                val allSuperTypes = it.getAllSuperTypes()
                allSuperTypes.any { superType ->
                    superType.declaration.qualifiedName?.asString() == topLevelClassFqn
                }
            }
            .toList()

        if (subclasses.isEmpty()) return emptyList()

        val file = codeGenerator.createNewFile(
            Dependencies(false),
            generatedPack,
            "${baseClass}Serializer"
        )

        file.bufferedWriter().use { writer ->
            writer.write("package $generatedPack\n\n")
            writer.write("import kotlinx.serialization.modules.SerializersModule\n")
            writer.write("import kotlinx.serialization.modules.polymorphic\n")
            writer.write("import kotlinx.serialization.modules.subclass\n")
            writer.write("import $topLevelClassFqn\n")

            subclasses.forEach { subclass ->
                writer.write("import ${subclass.qualifiedName?.asString()}\n")
            }

            writer.write(
                "\nval ${baseClass.replaceFirstChar { it.lowercase() }}SerializerModule = SerializersModule {\n"
            )
            writer.write("    polymorphic($baseClass::class) {\n")

            subclasses.forEach { subclass ->
                val serializer = subclass.annotations.firstOrNull {
                    it.shortName.getShortName() == "Serializable"
                }?.arguments?.find { it.name?.asString() == "with" }?.let { with ->
                    (with.value as? KSType)?.declaration?.qualifiedName?.asString()?.let {
                        if (it == "kotlinx.serialization.KSerializer") null else it
                    }
                }

                val name = subclass.simpleName.asString()
                if (serializer == null) {
                    writer.write("        subclass($name::class)\n")
                } else {
                    writer.write("        subclass($name::class, $serializer)\n")
                }
            }
            writer.write("    }\n")
            writer.write("}\n")
        }

        return emptyList()
    }
}