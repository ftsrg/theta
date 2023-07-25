package hu.bme.mit.theta.frontend.model

import Btor2BvSort
import Btor2Const

public interface Btor2NodeVisitor<R> {
    fun visit(node : Btor2UnaryOperation) : R
    fun visit(node : Btor2BinaryOperation) : R
    fun visit(node : Btor2TernaryOperation) : R
    fun visit(node : Btor2SliceOperation) : R
    fun visit(node : Btor2ExtOperation) : R
    fun visit(node : Btor2Const) : R
    fun visit(node : Btor2BvSort) : R
    fun visit(node : Btor2Input) : R
    fun visit(node : Btor2State) : R
    fun visit(node : Btor2Init) : R
    fun visit(node : Btor2Next) : R
    fun visit(node : Btor2Bad) : R
    fun visit(node : Btor2Constraint) : R
    fun visit(node : Btor2Output) : R
}