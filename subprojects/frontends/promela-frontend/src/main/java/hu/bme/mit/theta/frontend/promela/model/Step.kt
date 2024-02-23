package hu.bme.mit.theta.frontend.promela.model

sealed class Step()

data class StmntsStep(val stmnts : List<Statement>) : Step()

data class DeclListStep(val declLst : DeclList) : Step()

data class xrStep(val varrefs : List<VarRef>) : Step()

data class xsStep(val varrefs : List<VarRef>) : Step()