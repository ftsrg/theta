package hu.bme.mit.theta.frontend.promela.model

sealed class Module {
}

data class Proctype(
    val active: String?,
    val name: String,
    val declList: DeclList?,
    val priority: String?,
    val enabler: String?,
    val sequence: List<Statement>
) : Module()

data class Init(
    val priority: String?,
    val sequence: List<Statement>
) : Module()

data class Never(
    val sequence: List<Statement>
) : Module()

data class Trace(
    val sequence: List<Statement>
) : Module()

data class Utype(
    val name: String,
    val declList: DeclList
) : Module()

data class Mtype(
    val names: List<String>
) : Module()