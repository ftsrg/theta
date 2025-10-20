package hu.bme.mit.theta.frontend.promela.model

sealed class Statement

data class IfStatement(
    val options: PromelaOptions,
    val sequence: List<Statement>
) : Statement()

data class DoStatement(
    val options: PromelaOptions,
    val sequence: List<Statement>
) : Statement()

data class ForStatement(
    val range: Range,
    val sequence: List<Statement>
) : Statement()

data class AtomicStatement(
    val sequence: List<Statement>
) : Statement()

data class DStepStatement(
    val sequence: List<Statement>
) : Statement()

data class SelectStatement(
    val range: Range
) : Statement()

data class Sequence(
    val steps: List<Statement>
)

data class Range(
    val name: String,
    val start: String,
    val end: String
)

data class PromelaOptions(
    val sequences: List<Sequence>
)
