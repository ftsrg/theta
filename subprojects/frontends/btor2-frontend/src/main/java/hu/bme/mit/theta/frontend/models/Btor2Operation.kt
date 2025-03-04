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
            Btor2UnaryOperator.NOT -> TODO()
            Btor2UnaryOperator.INC -> TODO()
            Btor2UnaryOperator.DEC -> TODO()
            Btor2UnaryOperator.NEG -> TODO()
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
            else -> TODO()
        }
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    override fun getStmt(negate: Boolean): Stmt {
        return when(operator)
        {
            Btor2BinaryOperator.ADD -> AssignStmt.of(value, getExpr() as Expr<BvType>)
            else -> TODO()
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
            else -> TODO()
        }
    }

    override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param : P): R {
        return visitor.visit(this, param)
    }

    override fun getStmt(negate: Boolean): Stmt {
        val expr = when(operator)
        {
            Btor2ComparisonOperator.EQ -> getExpr() as Expr<BoolType>
            else -> TODO()
        }
        if(negate)
        {
            return AssumeStmt.of(NotExpr.of(expr))
        } else {
            return AssumeStmt.of(expr)
        }
    }
}

enum class Btor2UnaryOperator {
    NOT,
    INC,
    DEC,
    NEG
}

enum class Btor2ComparisonOperator {
    EQ,
    NEQ,
    SLT,
    SLE,
    SGT,
    SGTE,
    ULT,
    ULE,
    UGT,
    UGTE
}

enum class Btor2BinaryOperator {
    AND,
    NAND,
    NOR,
    OR,
    XOR,
    ADD,
    MUL,
    UDIV,
    UREM,
    SDIV,
    SREM,
    SMOD
}