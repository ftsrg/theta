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
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.*
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Eq
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Neg
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.TypeUtils.castBv
import java.math.BigInteger


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
        val one = BvExprs.Bv(booleanArrayOf(true)) as Expr<BvType>
        return when(operator)
        {
            Btor2UnaryOperator.NOT -> BvNotExpr.of(operand.getExpr() as Expr<BvType>)
            Btor2UnaryOperator.INC -> BvAddExpr.create(mutableListOf(operand.getExpr() as Expr<BvType>, one))
            Btor2UnaryOperator.DEC -> BvSubExpr.create(operand.getExpr() as Expr<BvType>, one)
            Btor2UnaryOperator.NEG -> BvNegExpr.of(operand.getExpr() as Expr<BvType>)
            Btor2UnaryOperator.REDAND -> BvAndExpr.create(valueByBits())
            Btor2UnaryOperator.REDOR -> BvOrExpr.create(valueByBits())
            Btor2UnaryOperator.REDXOR -> BvXorExpr.create(valueByBits())
        }
    }
    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    override fun getStmt(negate: Boolean): Stmt {
        TODO("Not yet implemented")
    }

    fun valueByBits() : List<Expr<BvType>> {
        val expr = operand.getExpr() as BvLitExpr
        val value = expr.value // BooleanArray
        val cut = mutableListOf<Expr<BvType>>()
        for (i in value.indices) {
            cut.add(BvLitExpr.of(booleanArrayOf(value[i])))
        }
        return cut
    }
}

data class Btor2ExtOperation(override val nid: UInt, override val sort : Btor2Sort, val operator: Btor2ExtOperator, val operand: Btor2Node, val w : UInt) : Btor2Operation(nid, sort)
{
    val value = Decls.Var("ext_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return value
    }

    override fun getExpr(): Expr<*> {
        return when(operator)
        {
            Btor2ExtOperator.SEXT -> TODO("Signed extension not implemented yet")
            Btor2ExtOperator.UEXT -> TODO("Unsigned extension not implemented yet")
        }
    }
    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    override fun getStmt(negate: Boolean): Stmt {
        TODO("Ext not yet implemented")
    }
}

data class Btor2SliceOperation(override val nid: UInt, override val sort : Btor2Sort, val operand: Btor2Node, val u : BigInteger, val l : BigInteger) : Btor2Operation(nid, sort)
{
    val value = Decls.Var("slice_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return value
    }

    override fun getExpr(): Expr<*> {
        val newU : BigInteger = u + BigInteger.valueOf(1)
        return BvExtractExpr.create(operand.getExpr() as Expr<BvType>, IntLitExpr.of(l), IntLitExpr.of(newU))
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    override fun getStmt(negate: Boolean): Stmt {
        return AssignStmt.of(value, getExpr() as Expr<BvType>)
    }
}

data class Btor2BinaryOperation(override val nid: UInt, override val sort : Btor2Sort, val operator: Btor2BinaryOperator, val op1: Btor2Node, val op2: Btor2Node, val opd1_negated: Boolean, val opd2_negated: Boolean) : Btor2Operation(nid, sort)
{
    val value = Decls.Var("binary_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return value
    }

    override fun getExpr(): Expr<*> {
        val op1_expr = if (opd1_negated) BvNotExpr.create(op1.getExpr() as Expr<BvType>) else op1.getExpr() as Expr<BvType>
        val op2_expr = if (opd2_negated) BvNotExpr.create(op2.getExpr() as Expr<BvType>) else op2.getExpr() as Expr<BvType>

        return when(operator)
        {
            Btor2BinaryOperator.ADD -> BvAddExpr.create(mutableListOf(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>))
            Btor2BinaryOperator.AND -> BvAndExpr.create(mutableListOf(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>))
            Btor2BinaryOperator.NAND -> BvNotExpr.create(BvAndExpr.create(mutableListOf(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)))
            Btor2BinaryOperator.NOR -> BvNotExpr.create(BvOrExpr.create(mutableListOf(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)))
            Btor2BinaryOperator.OR -> BvOrExpr.create(mutableListOf(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>))
            Btor2BinaryOperator.XNOR -> BvNotExpr.create(BvXorExpr.create(mutableListOf(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)))
            Btor2BinaryOperator.XOR -> BvXorExpr.create(mutableListOf(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>))
            Btor2BinaryOperator.MUL -> BvMulExpr.create(mutableListOf(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>))
            Btor2BinaryOperator.SUB -> BvSubExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)
            Btor2BinaryOperator.UDIV -> BvUDivExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)
            Btor2BinaryOperator.UREM -> BvURemExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)
            Btor2BinaryOperator.SDIV -> BvSDivExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)
            Btor2BinaryOperator.SREM -> BvSRemExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)
            Btor2BinaryOperator.SMOD -> BvSModExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)
            Btor2BinaryOperator.CONCAT -> BvConcatExpr.create(mutableListOf(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>))
            Btor2BinaryOperator.SADDO -> TODO("Signed addition with overflow not implemented yet")
            Btor2BinaryOperator.SDIVO -> TODO("Signed division with overflow not implemented yet")
            Btor2BinaryOperator.SMULO -> TODO("Signed multiplication with overflow not implemented yet")
            Btor2BinaryOperator.SSUBO -> TODO("Signed subtraction with overflow not implemented yet")
            Btor2BinaryOperator.UADDO -> TODO("Unsigned addition with overflow not implemented yet")
            Btor2BinaryOperator.UMULO -> TODO("Unsigned multiplication with overflow not implemented yet")
            Btor2BinaryOperator.USUBO -> TODO("Unsigned subtraction with overflow not implemented yet")
            Btor2BinaryOperator.ROL -> BvRotateLeftExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)
            Btor2BinaryOperator.ROR -> BvRotateRightExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)
            Btor2BinaryOperator.SLL -> BvShiftLeftExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)
            Btor2BinaryOperator.SRA -> BvArithShiftRightExpr.of(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)
            Btor2BinaryOperator.SRL -> BvLogicShiftRightExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>)
            Btor2BinaryOperator.READ -> TODO("Read operation not implemented yet")
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
            Btor2BinaryOperator.XNOR -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.XOR -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.MUL -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SUB -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.UDIV -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.UREM -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SDIV -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SREM -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SMOD -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.CONCAT -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SADDO -> TODO("Signed addition with overflow not implemented yet")
            Btor2BinaryOperator.SDIVO -> TODO("Signed division with overflow not implemented yet")
            Btor2BinaryOperator.SMULO -> TODO("Signed multiplication with overflow not implemented yet")
            Btor2BinaryOperator.SSUBO -> TODO("Signed subtraction with overflow not implemented yet")
            Btor2BinaryOperator.UADDO -> TODO("Unsigned addition with overflow not implemented yet")
            Btor2BinaryOperator.UMULO -> TODO("Unsigned multiplication with overflow not implemented yet")
            Btor2BinaryOperator.USUBO -> TODO("Unsigned subtraction with overflow not implemented yet")
            Btor2BinaryOperator.ROL -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.ROR -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SLL -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SRA -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.SRL -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            Btor2BinaryOperator.READ -> TODO("Read operation not implemented yet")
        }
    }
}

data class Btor2Comparison(override val nid: UInt, override val sort : Btor2Sort, val operator: Btor2ComparisonOperator, val op1: Btor2Node, val op2: Btor2Node, val opd1_negated: Boolean, val opd2_negated: Boolean) : Btor2Operation(nid, sort)
{
    val value = Decls.Var("comparison_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return value
    }

    override fun getExpr(): Expr<*> {
        val op1_expr = if (opd1_negated) BvNotExpr.create(op1.getExpr() as Expr<BvType>) else op1.getExpr() as Expr<BvType>
        val op2_expr = if (opd2_negated) BvNotExpr.create(op2.getExpr() as Expr<BvType>) else op2.getExpr() as Expr<BvType>
        return when(operator)
        {
            Btor2ComparisonOperator.EQ -> IteExpr.of(BvEqExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>),
                BvExprs.Bv(BooleanArray(1) { true }),
                BvExprs.Bv(BooleanArray(1) { false }))
                //Eq(op1_expr as RefExpr<BvType>, op2_expr as RefExpr<BvType>)
            Btor2ComparisonOperator.NEQ -> IteExpr.of(BvNeqExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>),
            BvExprs.Bv(BooleanArray(1) { true }),
            BvExprs.Bv(BooleanArray(1) { false }))
            Btor2ComparisonOperator.SLT -> IteExpr.of(BvSLtExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>),
            BvExprs.Bv(BooleanArray(1) { true }),
            BvExprs.Bv(BooleanArray(1) { false }))
            Btor2ComparisonOperator.SLTE -> IteExpr.of(BvSLeqExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>),
            BvExprs.Bv(BooleanArray(1) { true }),
            BvExprs.Bv(BooleanArray(1) { false }))
            Btor2ComparisonOperator.SGT -> IteExpr.of(BvSGtExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>),
            BvExprs.Bv(BooleanArray(1) { true }),
            BvExprs.Bv(BooleanArray(1) { false }))
            Btor2ComparisonOperator.SGTE -> IteExpr.of(BvSGeqExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>),
            BvExprs.Bv(BooleanArray(1) { true }),
            BvExprs.Bv(BooleanArray(1) { false }))
            Btor2ComparisonOperator.ULT -> IteExpr.of(BvULtExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>),
                BvExprs.Bv(BooleanArray(1) { true }),
                BvExprs.Bv(BooleanArray(1) { false }))
            Btor2ComparisonOperator.ULTE -> IteExpr.of(BvULeqExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>),
            BvExprs.Bv(BooleanArray(1) { true }),
            BvExprs.Bv(BooleanArray(1) { false }))
            Btor2ComparisonOperator.UGT -> IteExpr.of(BvUGtExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>),
            BvExprs.Bv(BooleanArray(1) { true }),
            BvExprs.Bv(BooleanArray(1) { false }))
            Btor2ComparisonOperator.UGTE -> IteExpr.of(BvUGeqExpr.create(op1_expr as Expr<BvType>, op2_expr as Expr<BvType>),
            BvExprs.Bv(BooleanArray(1) { true }),
            BvExprs.Bv(BooleanArray(1) { false }))
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
            Btor2ComparisonOperator.SLTE -> AssignStmt.of(value,getExpr() as Expr<BvType>)
            Btor2ComparisonOperator.SGT -> AssignStmt.of(value,getExpr() as Expr<BvType>)
            Btor2ComparisonOperator.SGTE -> AssignStmt.of(value,getExpr() as Expr<BvType>)
            Btor2ComparisonOperator.ULT -> AssignStmt.of(value,getExpr() as Expr<BvType>)
            Btor2ComparisonOperator.ULTE -> AssignStmt.of(value,getExpr() as Expr<BvType>)
            Btor2ComparisonOperator.UGT -> AssignStmt.of(value,getExpr() as Expr<BvType>)
            Btor2ComparisonOperator.UGTE -> AssignStmt.of(value,getExpr() as Expr<BvType>)
        }
    }
}

// Ehhez a nidhez vezetünk be egy változót, bekötjük
data class Btor2TernaryOperation(override val nid: UInt, override val sort: Btor2Sort, val operator: Btor2TernaryOperator,
    val op1: Btor2Node, val op2: Btor2Node, val op3: Btor2Node,
    val negated1: Boolean, val negated2: Boolean, val negated3: Boolean) : Btor2Operation(nid, sort)
{
    val value = Decls.Var("ternary_$nid", BvExprs.BvType(sort.width.toInt()))

    override fun getVar(): VarDecl<*>? {
        return value
    }

    override fun getExpr(): Expr<BvType> {
        //checkAllTypesEqual(op1.getExpr(), BvExprs.Bv(BooleanArray(1) { true }))
        val op1Expr = if (negated1) BvNotExpr.create(op1.getExpr() as Expr<BvType>) else (op1.getExpr() as Expr<BvType>)
        val op1ExprBool = Eq(op1Expr, BvExprs.Bv(BooleanArray(1) { true }))
        val op2Expr = if (negated2) BvNotExpr.create(op2.getExpr() as Expr<BvType>) else (op2.getExpr() as Expr<BvType> )
        val op3Expr = if (negated3) BvNotExpr.create(op3.getExpr() as Expr<BvType>) else (op3.getExpr() as Expr<BvType> )

        return when(operator)
        {
            Btor2TernaryOperator.ITE -> IteExpr.of(op1ExprBool as Expr<BoolType>, op2Expr as Expr<BvType>, op3Expr as Expr<BvType>)
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
            Btor2TernaryOperator.WRITE -> TODO("Write operation not implemented yet")
        }

    }
}