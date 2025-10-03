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
package hu.bme.mit.theta.xcfa

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.*
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.abstracttype.DivExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.ModExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.booltype.*
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.fptype.FpLitExpr
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.rattype.RatLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.FpUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType.CComplexTypeVisitor
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cbool.CBool
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CChar
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CUnsignedInt
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

private const val arraySize = 10

fun XCFA.toC(
  parseContext: ParseContext,
  arraySupport: Boolean,
  exactArraySupport: Boolean,
  intRangeConstraint: Boolean,
): String =
  """         
    extern void abort();
    extern unsigned short __VERIFIER_nondet_ushort();
    extern char __VERIFIER_nondet_char();
    extern short __VERIFIER_nondet_short();
    extern int __VERIFIER_nondet_int();
    extern _Bool __VERIFIER_nondet__Bool();
    extern void reach_error();
    
    ${
    if (procedures.any { it.vars.any { it.type is ArrayType<*, *> } }) if (arraySupport) if (exactArraySupport) """
        // "exact" array support
        typedef long unsigned int size_t;

        void * __attribute__((__cdecl__)) malloc (size_t __size) ;
        void __attribute__((__cdecl__)) free (void *) ;

        
        typedef struct
        {
          int *arr;
          int size;
          int def;
        } int_arr;

        int_arr array_write(int_arr arr, int idx, int val) {
            int_arr ret;
            ret.size = arr.size > idx + 1 ? arr.size : idx + 1;
            ret.arr = malloc(ret.size * sizeof(int));
            ret.def = arr.def;
            for(int i = 0; i < ret.size; ++i) {
                ret.arr[i] = i < arr.size ? arr.arr[i] : ret.def;
            }
            ret.arr[idx] = val;
            return ret;
        }

        int array_read(int_arr arr, int idx) {
            return idx < arr.size ? arr.arr[idx] : arr.def;
        }

        int array_equals(int_arr arr1, int_arr arr2) {
            int i = 0;
            if(arr1.def != arr2.def) return 0;
            for(; i < arr1.size; i++) {
                if(arr1.arr[i] != (i < arr2.size ? arr2.arr[i] : arr2.def)) return 0;
            }
            for(; i < arr2.size; i++) {
                if(arr2.arr[i] != arr1.def) return 0;
            }
            
            return 1;
        }
    """.trimIndent() else """
        // non-exact array support
        
        typedef struct
        {
          int arr[$arraySize];
        } int_arr;

        int_arr array_write(int_arr arr, int idx, int val) {
            arr.arr[idx] = val;
            return arr;
        }

        int array_read(int_arr arr, int idx) {
            return arr.arr[idx];
        }

        int array_equals(int_arr arr1, int_arr arr2) {
            for(int i = 0; i < $arraySize; i++) {
                if(arr1.arr[i] != arr2.arr[i]) return 0;
            }
            return 1;
        }        
    """.trimIndent() else error("Array support not enabled") else ""
}
    
    ${procedures.joinToString("\n\n") { it.decl(parseContext) + ";" }}
    
    ${procedures.joinToString("\n\n") { it.def(parseContext, intRangeConstraint) }}
    
    ${
    if (initProcedures.size != 1) error("Exactly one initial procedure is supported.") else {
        val proc = initProcedures[0]
        val procName = proc.first.name.toC()
        if (procName != "main")
            "int main() { $procName(${proc.second.joinToString(", ") { it.toC(parseContext) }}); }"
        else ""
    }
}

"""
    .trimIndent()

fun XcfaProcedure.decl(parseContext: ParseContext): String =
  if (params.isNotEmpty()) {
    "${CComplexType.getType(params[0].first.ref, parseContext).toC()} ${name.toC()}(${
            params.subList(1, params.size).joinToString(", ") { it.decl(parseContext) }
        })"
  } else {
    "void ${name.toC()}()"
  }

private fun VarDecl<*>.unsafeBounds(parseContext: ParseContext) =
  CComplexType.getType(ref, parseContext)
    .accept(
      object : CComplexTypeVisitor<Unit, Expr<BoolType>?>() {
        override fun visit(type: CInteger, param: Unit): Expr<BoolType>? {
          return Or(Leq(ref, Int(-1_000_000_000)), Geq(ref, Int(1_000_000_000)))
        }

        override fun visit(type: CBool?, param: Unit?): Expr<BoolType>? {
          return null
        }
      },
      Unit,
    )

private fun Set<VarDecl<*>>.unsafeBounds(
  parseContext: ParseContext,
  intRangeConstraint: Boolean,
): String {
  if (!intRangeConstraint) return ""

  val conditions = this.map { (it.unsafeBounds(parseContext))?.toC(parseContext) }.filterNotNull()
  return if (conditions.isNotEmpty()) "if (" + conditions.joinToString(" || ") + ") abort();"
  else ""
}

fun XcfaProcedure.def(parseContext: ParseContext, intRangeConstraint: Boolean): String =
  """
    ${decl(parseContext)} {
        // return parameter
        ${if (params.isNotEmpty()) params[0].decl(parseContext) + ";" else ""}
        
        // variables
        ${(vars - params.map { it.first }.toSet()).joinToString("\n") { it.decl(parseContext) + ";" }}
        
        ${vars.unsafeBounds(parseContext, intRangeConstraint)}
        
        // main logic
        goto ${initLoc.name.toC()};
        
        ${
    locs.joinToString("\n") {
        """
                    ${it.name.toC()}:
                    ${it.toC(parseContext, intRangeConstraint)}
                """.trimIndent()
    }
}
        
        // return expression
        ${if (params.isNotEmpty()) "return " + params[0].first.name.toC() + ";" else ""}
    }
"""
    .trimIndent()

private fun XcfaLocation.toC(parseContext: ParseContext, intRangeConstraint: Boolean): String =
  if (this.error) {
    "reach_error();"
  } else
    when (outgoingEdges.size) {
      0 -> "goto ${name.toC()};"
      1 ->
        outgoingEdges.first().getFlatLabels().joinToString("\n") {
          it.toC(parseContext, intRangeConstraint)
        } + " goto ${outgoingEdges.first().target.name.toC()};"

      2 ->
        """
                switch(__VERIFIER_nondet__Bool()) {
                ${
                outgoingEdges.mapIndexed { index, xcfaEdge ->
                    "case $index: \n" +
                        xcfaEdge.getFlatLabels()
                            .joinToString("\n", postfix = "\n") { it.toC(parseContext, intRangeConstraint) } +
                        "goto ${xcfaEdge.target.name.toC()};\n"
                }.joinToString("\n")
            }
                default: abort();
                }
            """
          .trimIndent()

      else ->
        """
                switch(__VERIFIER_nondet_int()) {
                ${
                outgoingEdges.mapIndexed { index, xcfaEdge ->
                    "case $index: \n" +
                        xcfaEdge.getFlatLabels()
                            .joinToString("\n", postfix = "\n") { it.toC(parseContext, intRangeConstraint) } +
                        "goto ${xcfaEdge.target.name.toC()};\n"
                }.joinToString("\n")
            }
                default: abort();
                }
            """
          .trimIndent()
    }

private fun XcfaLabel.toC(parseContext: ParseContext, intRangeConstraint: Boolean): String =
  when (this) {
    is StmtLabel -> this.toC(parseContext, intRangeConstraint)
    is SequenceLabel -> labels.joinToString("\n") { it.toC(parseContext, intRangeConstraint) }
    is InvokeLabel ->
      "${params[0].toC(parseContext)} = ${name.toC()}(${
            params.subList(1, params.size).map { it.toC(parseContext) }.joinToString(", ")
        });"

    else -> TODO("Not yet supported: $this")
  }

private fun StmtLabel.toC(parseContext: ParseContext, intRangeConstraint: Boolean): String =
  when (stmt) {
    is HavocStmt<*> ->
      "${stmt.varDecl.name.toC()} = __VERIFIER_nondet_${
            CComplexType.getType(stmt.varDecl.ref, parseContext).toC()
        }(); ${setOf(stmt.varDecl).unsafeBounds(parseContext, intRangeConstraint)}"

    is AssignStmt<*> -> "${stmt.varDecl.name.toC()} = ${stmt.expr.toC(parseContext)};"
    is MemoryAssignStmt<*, *, *> ->
      "${stmt.deref.toC(parseContext)} = ${stmt.expr.toC(parseContext)};"
    is AssumeStmt -> "if(!${stmt.cond.toC(parseContext)}) abort();"
    else -> TODO("Not yet supported: $stmt")
  }

fun Pair<VarDecl<*>, ParamDirection>.decl(parseContext: ParseContext): String =
  //    if(second == ParamDirection.IN) {
  first.decl(parseContext)

//    } else error("Only IN params are supported right now")

fun VarDecl<*>.decl(parseContext: ParseContext): String =
  "${CComplexType.getType(ref, parseContext).toC()} ${name.toC()}"

private fun CComplexType.toC(): String =
  when (this) {
    is CArray -> "${this.embeddedType.toC()}_arr"
    is CSignedInt -> "int"
    is CUnsignedInt -> "unsigned int"
    is CChar -> "char"
    is CBool -> "_Bool"
    else -> this.typeName
  }

// below functions implement the serialization of expressions to C-style expressions
fun Expr<*>.toC(parseContext: ParseContext) =
  when (this) {
    is NullaryExpr<*> -> this.toC(parseContext)
    is UnaryExpr<*, *> -> this.toC(parseContext)
    is BinaryExpr<*, *> -> this.toC(parseContext)
    is MultiaryExpr<*, *> -> this.toC(parseContext)
    is ArrayWriteExpr<*, *> -> this.toC(parseContext)
    is ArrayReadExpr<*, *> -> this.toC(parseContext)
    is Dereference<*, *, *> -> this.toC(parseContext)
    is IteExpr<*> -> this.toC(parseContext)
    else -> TODO("Not yet supported: $this")
  }

fun Dereference<*, *, *>.toC(parseContext: ParseContext): String = "$array[$offset]"

fun ArrayWriteExpr<*, *>.toC(parseContext: ParseContext): String =
  "array_write(${this.array.toC(parseContext)}, ${this.index.toC(parseContext)}, ${this.elem.toC(parseContext)})"

fun ArrayReadExpr<*, *>.toC(parseContext: ParseContext): String =
  "array_read(${this.array.toC(parseContext)}, ${this.index.toC(parseContext)})"

fun IteExpr<*>.toC(parseContext: ParseContext): String =
  "(${this.cond.toC(parseContext)} ? ${this.then.toC(parseContext)} : ${this.`else`.toC(parseContext)})"

// nullary: ref + lit
fun NullaryExpr<*>.toC(parseContext: ParseContext): String =
  when (this) {
    is RefExpr<*> -> this.decl.name.toC()
    is LitExpr<*> -> (this as LitExpr<*>).toC(parseContext)
    else -> TODO("Not yet supported: $this")
  }

fun LitExpr<*>.toC(parseContext: ParseContext): String =
  when (this) {
    is FalseExpr -> "0"
    is TrueExpr -> "1"
    is IntLitExpr -> this.value.toString()
    is RatLitExpr -> "(${this.num}.0/${this.denom}.0)"
    is FpLitExpr -> FpUtils.fpLitExprToBigFloat(FpRoundingMode.RNE, this).toString()
    is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(this).toString()
    else -> error("Not supported: $this")
  }

fun UnaryExpr<*, *>.toC(parseContext: ParseContext): String =
  "(${this.cOperator()} ${op.toC(parseContext)})"

fun BinaryExpr<*, *>.toC(parseContext: ParseContext): String =
  if (leftOp.type is ArrayType<*, *>) {
    "${this.arrayCOperator()}(${leftOp.toC(parseContext)}, ${rightOp.toC(parseContext)})"
  } else if (this is ModExpr<*>) {
    "( (${leftOp.toC(parseContext)} % ${rightOp.toC(parseContext)} + ${rightOp.toC(parseContext)}) % ${
            rightOp.toC(parseContext)
        } )"
  } else {
    "(${leftOp.toC(parseContext)} ${this.cOperator()} ${rightOp.toC(parseContext)})"
  }

fun MultiaryExpr<*, *>.toC(parseContext: ParseContext): String =
  ops.joinToString(separator = " ${this.cOperator()} ", prefix = "(", postfix = ")") {
    it.toC(parseContext)
  }

fun Expr<*>.cOperator() =
  when (this) {
    is EqExpr<*> -> "=="
    is NeqExpr<*> -> "!="
    is OrExpr -> "||"
    is AndExpr -> "&&"
    is NotExpr -> "!"
    // is ModExpr<*> -> "%" // handled above
    is DivExpr<*> -> "/"

    is UnaryExpr<*, *> -> operatorLabel
    is BinaryExpr<*, *> -> operatorLabel
    is MultiaryExpr<*, *> -> operatorLabel
    else -> TODO("Not yet implemented operator label for expr: $this")
  }

fun Expr<*>.arrayCOperator() =
  when (this) {
    is EqExpr<*> -> "array_equals"
    is NeqExpr<*> -> "!array_equals"
    else -> TODO("Not yet implemented array operator label for expr: $this")
  }

fun String.toC() = this.replace(Regex("[^A-Za-z_0-9]"), "_")
