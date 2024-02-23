package hu.bme.mit.theta.frontend.promela.model

sealed class Module {
}

data class Proctype(
    val active: String?,
    val name: String,
    val declList: DeclList?,
    val priority: String?,
    val enabler: String?,
    val sequence: List<Step>
) : Module()

data class Init(
    val priority: String?,
    val sequence: List<Step>
) : Module()

data class Never(
    val sequence: List<Step>
) : Module()

data class Trace(
    val sequence: List<Step>
) : Module()

data class Utype(
    val name: String,
    val declList: DeclList
) : Module()

data class Mtype(
    val names: List<String>
) : Module()

data class DeclList(val declarations: List<Declaration>)

sealed class Declaration

data class TypedDeclaration(
    val visible: String?,
    val typeName: String,
    val variables: List<Variable>
) : Declaration()

data class UnsignedDeclaration(
    val name: String,
    val const: String,
    val initialValue: Any? // This can be modified based on your specific logic
) : Declaration()

data class Variable(
    val name: String,
    val arraySize: String?, // You might want to change the type if it's not a String
    val initialValue: Any? // This can be modified based on your specific logic
)