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
package hu.bme.mit.theta.ksp

import com.google.devtools.ksp.getAllSuperTypes
import com.google.devtools.ksp.isAbstract
import com.google.devtools.ksp.processing.*
import com.google.devtools.ksp.symbol.*

class PolymorphicModuleProcessor(
    private val codeGenerator: CodeGenerator,
    private val pack: String,
    private val baseClass: String,
) : SymbolProcessor {

    override fun process(resolver: Resolver): List<KSAnnotated> {
        val topLevelClassFqn = "$pack.$baseClass"
        val generatedPack = "$pack.generated"

        val subclasses = resolver.getAllFiles().flatMap { file ->
            file.declarations
                .filterIsInstance<KSClassDeclaration>()
                .filter { !it.isAbstract() && it.getSealedSubclasses().toList().isEmpty() }
                .filter { clazz ->
                    clazz.annotations.any {
                        it.annotationType.resolve().declaration.qualifiedName?.asString() == "kotlinx.serialization.Serializable"
                    }
                }
                .filter {
                    val allSuperTypes = it.getAllSuperTypes()
                    allSuperTypes.any { superType ->
                        superType.declaration.qualifiedName?.asString() == topLevelClassFqn
                    }
                }
        }.toList()

        if (subclasses.isEmpty()) return emptyList()

        val inputFiles = subclasses.mapNotNull { it.containingFile }.distinct()
        val file = try {
            codeGenerator.createNewFile(
                Dependencies(false, *inputFiles.toTypedArray()),
                generatedPack,
                "${baseClass}Serializer"
            )
        } catch (e: FileAlreadyExistsException) {
            return emptyList()
        }

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