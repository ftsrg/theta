/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.frontend.models

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.NegExpr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.bvtype.*


abstract class Btor2Operation(id: UInt, sort: Btor2Sort) : Btor2Node(id, sort)
{
    abstract fun getStmt(negate: Boolean): Stmt

}
// Operators
data class Btor2UnaryOperation(override val nid: UInt, override val sort : Btor2Sort, val operator: Btor2UnaryOperator, val operand: Btor2Node) : Btor2Operation(nid, sort)
{
    val value = Decls.Var("unary_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return value
    }

    override fun getExpr(): Expr<*> {
        return when(operator)
        {
            Btor2UnaryOperator.NOT -> BvNotExpr.of(operand.getExpr() as Expr<BvType>)
            Btor2UnaryOperator.INC -> TODO()
            Btor2UnaryOperator.DEC -> TODO()
            Btor2UnaryOperator.NEG -> TODO()
            Btor2UnaryOperator.REDAND -> TODO()
            Btor2UnaryOperator.REDOR -> TODO()
            Btor2UnaryOperator.REDXOR -> TODO()
        }
    }
    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    override fun getStmt(negate: Boolean): Stmt {
        TODO("Not yet implemented")
    }
}

data class Btor2ExtOperation(override val nid: UInt, override val sort : Btor2Sort, val operand: Btor2Node, val w : UInt) : Btor2Operation(nid, sort)
{
    val value = Decls.Var("ext_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return value
    }

    override fun getExpr(): Expr<*> {
        TODO("Not yet implemented")
    }
    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    override fun getStmt(negate: Boolean): Stmt {
        TODO("Not yet implemented")
    }
}

data class Btor2SliceOperation(override val nid: UInt, override val sort : Btor2Sort, val operand: Btor2Node, val u : UInt, val l : UInt) : Btor2Operation(nid, sort)
{
    val value = Decls.Var("slice_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return value
    }

    override fun getExpr(): Expr<*> {
        TODO("Not yet implemented")
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    override fun getStmt(negate: Boolean): Stmt {
        TODO("Not yet implemented")
    }
}

data class Btor2BinaryOperation(override val nid: UInt, override val sort : Btor2Sort, val operator: Btor2BinaryOperator, val op1: Btor2Node, val op2: Btor2Node) : Btor2Operation(nid, sort)
{
    val value = Decls.Var("binary_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return value
    }

    override fun getExpr(): Expr<*> {
        return when(operator)
        {
            Btor2BinaryOperator.ADD -> BvAddExpr.of(mutableListOf(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>))
            Btor2BinaryOperator.AND -> BvAndExpr.of(mutableListOf(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>))
            Btor2BinaryOperator.NAND -> NotExpr.of(BvAndExpr.of(mutableListOf(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>)) as Expr<BoolType>)
            Btor2BinaryOperator.NOR -> NotExpr.of(BvOrExpr.of(mutableListOf(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>)) as Expr<BoolType>)
            Btor2BinaryOperator.OR -> BvOrExpr.of(mutableListOf(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>))
            Btor2BinaryOperator.XOR -> BvXorExpr.of(mutableListOf(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>))
            Btor2BinaryOperator.MUL -> BvMulExpr.of(mutableListOf(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>))
            Btor2BinaryOperator.UDIV -> BvUDivExpr.of(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>)
            Btor2BinaryOperator.UREM -> BvURemExpr.of(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SDIV -> BvSDivExpr.of(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SREM -> BvSRemExpr.of(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SMOD -> BvSModExpr.of(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>)
            Btor2BinaryOperator.CONCAT -> BvConcatExpr.of(mutableListOf(op1.getExpr() as Expr<BvType>, op2.getExpr() as Expr<BvType>))
            Btor2BinaryOperator.SADDO -> TODO()
            Btor2BinaryOperator.SDIVO -> TODO()
            Btor2BinaryOperator.SMULO -> TODO()
            Btor2BinaryOperator.SSUBO -> TODO()
            Btor2BinaryOperator.UADDO -> TODO()
            Btor2BinaryOperator.UMULO -> TODO()
            Btor2BinaryOperator.USUBO -> TODO()
            Btor2BinaryOperator.ROL -> TODO()
            Btor2BinaryOperator.ROR -> TODO()
            Btor2BinaryOperator.SLL -> TODO()
            Btor2BinaryOperator.SRA -> TODO()
            Btor2BinaryOperator.SRL -> TODO()
            Btor2BinaryOperator.READ -> TODO()
        }
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    override fun getStmt(negate: Boolean): Stmt {
        return when(operator)
        {
            Btor2BinaryOperator.ADD -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.AND -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.NAND -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.NOR -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.OR -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.XOR -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.MUL -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.UDIV -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.UREM -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SDIV -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SREM -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SMOD -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.CONCAT -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SADDO -> TODO()
            Btor2BinaryOperator.SDIVO -> TODO()
            Btor2BinaryOperator.SMULO -> TODO()
            Btor2BinaryOperator.SSUBO -> TODO()
            Btor2BinaryOperator.UADDO -> TODO()
            Btor2BinaryOperator.UMULO -> TODO()
            Btor2BinaryOperator.USUBO -> TODO()
            Btor2BinaryOperator.ROL -> TODO()
            Btor2BinaryOperator.ROR -> TODO()
            Btor2BinaryOperator.SLL -> TODO()
            Btor2BinaryOperator.SRA -> TODO()
            Btor2BinaryOperator.SRL -> TODO()
            Btor2BinaryOperator.READ -> TODO()
        }
    }
}

data class Btor2Comparison(override val nid: UInt, override val sort : Btor2Sort, val operator: Btor2ComparisonOperator, val op1: Btor2Node, val op2: Btor2Node) : Btor2Operation(nid, sort)
{
    val value = Decls.Var("comparison_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return value
    }

    override fun getExpr(): Expr<*> {
        return when(operator)
        {
            Btor2ComparisonOperator.EQ -> BvEqExpr.of(op1.getExpr() as Expr<BvType> , op2.getExpr()as Expr<BvType>)
            Btor2ComparisonOperator.NEQ -> BvNeqExpr.of(op1.getExpr() as Expr<BvType> , op2.getExpr()as Expr<BvType>)
            Btor2ComparisonOperator.SLT -> BvSLtExpr.of(op1.getExpr() as Expr<BvType> , op2.getExpr()as Expr<BvType>)
            Btor2ComparisonOperator.SLTE -> TODO()
            Btor2ComparisonOperator.SGT -> TODO()
            Btor2ComparisonOperator.SGTE -> TODO()
            Btor2ComparisonOperator.ULT -> TODO()
            Btor2ComparisonOperator.ULTE -> TODO()
            Btor2ComparisonOperator.UGT -> TODO()
            Btor2ComparisonOperator.UGTE -> TODO()
        }
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    override fun getStmt(negate: Boolean): Stmt {
        return when(operator)
        {
            Btor2ComparisonOperator.EQ -> AssignStmt.of(value,getExpr() as Expr<BvType>)
            Btor2ComparisonOperator.NEQ -> AssignStmt.of(value,getExpr() as Expr<BvType>)
            Btor2ComparisonOperator.SLT -> AssignStmt.of(value,getExpr() as Expr<BvType>)
            Btor2ComparisonOperator.SLTE -> TODO()
            Btor2ComparisonOperator.SGT -> TODO()
            Btor2ComparisonOperator.SGTE -> TODO()
            Btor2ComparisonOperator.ULT -> TODO()
            Btor2ComparisonOperator.ULTE -> TODO()
            Btor2ComparisonOperator.UGT -> TODO()
            Btor2ComparisonOperator.UGTE -> TODO()
        }
    }
}

// Ehhez a nidhez vezetünk be egy változót, bekötjük
data class Btor2TernaryOperation(override val nid: UInt, override val sort: Btor2Sort, val operator: Btor2TernaryOperator,
    val op1: Btor2Node, val op2: Btor2Node, val op3: Btor2Node, val negated: Boolean) : Btor2Operation(nid, sort)
{
    val value = Decls.Var("ternary_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return value
    }

    override fun getExpr(): Expr<*> {
        val op1_expr : Expr<BoolType>
        if (negated) {
            op1_expr = NotExpr.of(op1.getExpr() as Expr<BoolType>)
        }
        else {
            op1_expr = op1.getExpr() as Expr<BoolType>
        }
        return when(operator)
        {
            Btor2TernaryOperator.ITE -> IteExpr.of(op1_expr, op2.getExpr() as Expr<BvType>, op3.getExpr() as Expr<BvType>)
            Btor2TernaryOperator.WRITE -> TODO()
        }
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    override fun getStmt(negate: Boolean): Stmt {
        return when(operator)
        {
            Btor2TernaryOperator.ITE -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2TernaryOperator.WRITE -> TODO()
        }

    }
}