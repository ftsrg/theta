package hu.bme.mit.theta.frontend.promela.model
sealed class Step

data class IfStatement(
    val options: PromelaOptions,
    val sequence: List<Step>
) : Step()

data class DoStatement(
    val options: PromelaOptions,
    val sequence: List<Step>
) : Step()

data class ForStatement(
    val range: Range,
    val sequence: List<Step>
) : Step()

data class AtomicStatement(
    val sequence: List<Step>
) : Step()

data class DStepStatement(
    val sequence: List<Step>
) : Step()

data class SelectStatement(
    val range: Range
) : Step()

data class Sequence(
    val steps: List<Step>
)

data class Range(
    val name: String,
    val start: String,
    val end: String
)

data class PromelaOptions(
    val sequences: List<Sequence>
)
