package hu.bme.mit.theta.frontend.promela.model

// TODO static var list?
data class Variable(val name : String) {
    lateinit var type : String
}

data class VariableInitialization(val variable: Variable, val initExpr : PromelaExpression) {

} // TODO ch_init