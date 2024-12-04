package hu.bme.mit.theta.frontend.promela.model

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

class OneDecl