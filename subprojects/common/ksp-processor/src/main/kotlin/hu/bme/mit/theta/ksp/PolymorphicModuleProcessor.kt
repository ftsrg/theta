package hu.bme.mit.theta.ksp

import com.google.devtools.ksp.getAllSuperTypes
import com.google.devtools.ksp.isAbstract
import com.google.devtools.ksp.processing.*
import com.google.devtools.ksp.symbol.*

class PolymorphicModuleProcessor(
    private val codeGenerator: CodeGenerator,
    private val logger: KSPLogger,
    private val pack: String,
    private val topLevelClass: String,
) : SymbolProcessor {

    override fun process(resolver: Resolver): List<KSAnnotated> {
        val topLevelClassFqn = "$pack.$topLevelClass"
        val generatedPack = "$pack.generated"

        val subclasses = resolver
            .getSymbolsWithAnnotation("kotlinx.serialization.Serializable")
            .filterIsInstance<KSClassDeclaration>()
            .filter { !it.isAbstract() }
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
            "${topLevelClass}Serializer"
        )

        file.bufferedWriter().use { writer ->
            writer.write("package $generatedPack\n\n")
            writer.write("import kotlinx.serialization.KSerializer\n")
            writer.write("import kotlinx.serialization.PolymorphicSerializer\n")
            writer.write("import kotlinx.serialization.descriptors.SerialDescriptor\n")
            writer.write("import kotlinx.serialization.descriptors.buildClassSerialDescriptor\n")
            writer.write("import kotlinx.serialization.descriptors.element\n")
            writer.write("import kotlinx.serialization.encoding.*\n")
            writer.write("import kotlinx.serialization.modules.SerializersModule\n")
            writer.write("import kotlinx.serialization.modules.polymorphic\n")
            writer.write("import kotlinx.serialization.modules.subclass\n")
            writer.write("import $topLevelClassFqn\n")

            subclasses.forEach { subclass ->
                writer.write("import ${subclass.qualifiedName?.asString()}\n")
            }

            writer.write(
                "\nval ${topLevelClass.replaceFirstChar { it.lowercase() }}SerializerModule = SerializersModule {\n"
            )
            writer.write("    polymorphic($topLevelClass::class) {\n")

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

            subclasses.filter { it.typeParameters.isNotEmpty() }.forEach { subclass ->
                val name = subclass.simpleName.asString()
                logger.warn("$name -> ${subclass.typeParameters[0].bounds.toList()}")
                val typeParams = subclass.typeParameters.joinToString(", ") {
                    val bounds = it.bounds.toList()
                    require(bounds.size <= 1) {
                        "Serializer class generation: multiple bounds not supported for type parameters."
                    }
                    "out ${bounds.firstOrNull()?.toString() ?: "Any?"}"
                }

                writer.write("\n\nclass ${name}Serializer : KSerializer<$name<$typeParams>> {\n\n")
                writer.write(
                    "    override val descriptor: SerialDescriptor = buildClassSerialDescriptor(\"$name\") {\n"
                )

                val parameters = subclass.primaryConstructor!!.parameters.map { parameter ->
                    val typeName = parameter.type.toString()
                    val type = subclass.typeParameters.find { it.name.asString() == typeName }?.bounds?.firstOrNull()
                        ?: typeName
                    parameter.name!!.asString() to type
                }
                parameters.forEach { (name, _) ->
                    writer.write("        element<String>(\"$name\")\n")
                }
                writer.write("    }\n\n")

                writer.write("    override fun serialize(encoder: Encoder, value: $name<$typeParams>) =\n")
                writer.write("        encoder.encodeStructure(descriptor) {\n")
                parameters.forEachIndexed { index, (name, type) ->
                    writer.write(
                        "            encodeSerializableElement(descriptor, $index, PolymorphicSerializer($type::class), value.$name)\n"
                    )
                }
                writer.write("        }\n")

                writer.write(
                    "    override fun deserialize(decoder: Decoder): $name<$typeParams> = decoder.decodeStructure(descriptor) {\n"
                )
                parameters.forEach { (name, type) ->
                    writer.write("        var $name: $type? = null\n")
                }
                writer.write("        while (true) {\n")
                writer.write("            when (val index = decodeElementIndex(descriptor)) {\n")
                parameters.forEachIndexed { index, (name, type) ->
                    writer.write(
                        "                $index -> $name = decodeSerializableElement(descriptor, 0, PolymorphicSerializer($type::class))\n"
                    )
                }
                writer.write("                CompositeDecoder.DECODE_DONE -> break\n")
                writer.write("                else -> error(\"Unexpected index: \$index\")")
                writer.write("            }\n")
                writer.write("        }\n")
                writer.write("        $name(\n")
                parameters.forEach { (name, _) ->
                    writer.write("            $name = $name ?: error(\"Missing $name\"),\n")
                }
                writer.write("        )\n")
                writer.write("    }\n")

                writer.write("}\n")
            }
        }

        return emptyList()
    }
}