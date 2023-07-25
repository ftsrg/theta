package hu.bme.mit.theta.frontend.model

import Btor2BvSort
import Btor2Const

public interface Btor2NodeVisitor<R, P> {
    fun visit(node: Btor2UnaryOperation, param: P) : R
    fun visit(node: Btor2BinaryOperation, param: P) : R
    fun visit(node: Btor2TernaryOperation, param: P) : R
    fun visit(node: Btor2SliceOperation, param: P) : R
    fun visit(node: Btor2ExtOperation, param: P) : R
    fun visit(node: Btor2Const, param: P) : R
    fun visit(node: Btor2BvSort, param: P) : R
    fun visit(node: Btor2Input, param: P) : R
    fun visit(node: Btor2State, param: P) : R
    fun visit(node: Btor2Init, param: P) : R
    fun visit(node: Btor2Next, param: P) : R
    fun visit(node: Btor2Bad, param: P) : R
    fun visit(node: Btor2Constraint, param: P) : R
    fun visit(node: Btor2Output, param: P) : R
}