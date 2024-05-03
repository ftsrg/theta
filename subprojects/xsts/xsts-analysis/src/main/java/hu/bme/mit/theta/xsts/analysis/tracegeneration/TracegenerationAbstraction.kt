package hu.bme.mit.theta.xsts.analysis.tracegeneration

enum class TracegenerationAbstraction {
    NONE,
    VARLIST, // explicit
    AUTOPRED // Cartesian predicates based on guards
}