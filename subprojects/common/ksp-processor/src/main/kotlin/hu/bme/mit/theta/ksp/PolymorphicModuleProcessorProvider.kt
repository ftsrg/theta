package hu.bme.mit.theta.ksp

import com.google.devtools.ksp.processing.*

sealed class PolymorphicModuleProcessorProvider(
    private val pack: String,
    private val baseClass: String,
) : SymbolProcessorProvider {
    override fun create(environment: SymbolProcessorEnvironment): SymbolProcessor =
        PolymorphicModuleProcessor(environment.codeGenerator, environment.logger, pack, baseClass)
}

class TypeSerializerProcessorProvider :
    PolymorphicModuleProcessorProvider("hu.bme.mit.theta.core.type", "Type")

class DeclSerializerProcessorProvider :
    PolymorphicModuleProcessorProvider("hu.bme.mit.theta.core.decl", "Decl")

class StmtSerializerProcessorProvider :
    PolymorphicModuleProcessorProvider("hu.bme.mit.theta.core.stmt", "Stmt")

class ExprSerializerProcessorProvider :
    PolymorphicModuleProcessorProvider("hu.bme.mit.theta.core.type", "Expr")
