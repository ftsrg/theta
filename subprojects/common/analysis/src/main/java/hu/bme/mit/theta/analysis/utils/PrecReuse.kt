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

package hu.bme.mit.theta.analysis.utils

import com.google.common.base.Preconditions
import com.google.common.collect.Lists
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.rattype.RatExprs
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel
import hu.bme.mit.theta.solver.smtlib.solver.parser.GeneralResponse
import hu.bme.mit.theta.solver.smtlib.solver.parser.PrecisionResponse
import hu.bme.mit.theta.solver.smtlib.solver.parser.ThrowExceptionErrorListener
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.File

object PrecReuse {
    private var isEnabled = false
    private var inputFile: File? = null
    private var serializer: PrecSerializer<Prec>? = null
    private var toSave: Prec? = null

    fun enable(precSerializer: PrecSerializer<*>) {
        isEnabled = true
        serializer = precSerializer
    }

    fun setInput(precFile: File) {
        inputFile = precFile
    }

    fun <P : Prec> load(currentVars: Iterable<VarDecl<*>> = listOf()): P {
        assert(isEnabled)
        assert(inputFile != null)
        assert(serializer != null)

        val savedPrec = (if (isEnabled) inputFile?.readText() else null) ?: ""
        return serializer?.parse(savedPrec, currentVars) as? P ?: throw RuntimeException("Misconfigured PrecSerializer")
    }

    fun <P : Prec> store(prec: P) {
        toSave = prec
    }

    fun writeTo(outputFolder: File) {
        assert(serializer != null)
        if (!isEnabled) return

        val outputFile = File(outputFolder, "prec.txt")
        outputFile.writeText(toSave?.let{ serializer!!.serialize(it) } ?: "")
    }

}

interface PrecSerializer<out P : Prec> {
    fun serialize(prec: Prec): String
    fun parse(input: String, currentVars: Iterable<VarDecl<*>>): P
}

class ExplPrecSerializer : PrecSerializer<ExplPrec> {
    override fun serialize(prec: Prec) = prec.usedVars.joinToString(separator = " ") { it.toSymbol() }
    override fun parse(input: String, currentVars: Iterable<VarDecl<*>>): ExplPrec {
        val varNames = input.trim().split(Regex("\\s+"))
        val vars = currentVars.filter { varNames.contains(it.toSymbol()) }
        return ExplPrec.of(vars)
    }
}

class PredPrecSerializer : PrecSerializer<PredPrec> {
    override fun serialize(prec: Prec): String {
        val varDecls = prec.usedVars.joinToString(separator = "\n") { "(declare-fun ${it.toSymbol()} () ${it.type})" }
        val quotedVarLookup = prec.usedVars
            .filter { it.toSymbol() != it.name }
            .associateWith { Decls.Var(it.toSymbol(), it.type) }

        val predicates = (prec as PredPrec).preds
            .map { pred -> ExprUtils.changeDecls(pred, quotedVarLookup) }
            .let { quotedPreds -> Utils.lispStringBuilder().addAll(quotedPreds).toString() }
            .let { it.slice(1..(it.length - 2)) }

        return "$varDecls\n$predicates"
    }

    override fun parse(input: String, currentVars: Iterable<VarDecl<*>>): PredPrec {
        val symbolTable = PrecSmtLibSymbolTable()
        val termTransformer = GenericSmtLibTermTransformer(symbolTable)

        val savedPrec = parseResponse(input)
        val funDecls = savedPrec.funDeclarations

        funDecls.forEach { (name, def) ->
            var type = transformSort(def.get2())
            for (s in Lists.reverse(def.get1())) {
                type = FuncType.of(transformSort(s), type)
            }
            symbolTable.put(Decls.Const(name, type), name, def.get3())
        }

        val varLookup = funDecls.keys
            .associateBy(symbolTable::getConst) { name -> currentVars.find { it.toSymbol() == name } }
            .filterValues { it != null }

        val preds = savedPrec.terms.map { t ->
            val expr = termTransformer.toExpr(t, BoolExprs.Bool(), SmtLibModel(emptyMap()))
            ExprUtils.changeDecls(expr, varLookup)
        }
        return PredPrec.of(preds)
    }
}

class PrecSmtLibSymbolTable : GenericSmtLibSymbolTable() {
    override fun put(constDecl: ConstDecl<*>, symbol: String, declaration: String) {
        Preconditions.checkState(!constToSymbol.containsKey(constDecl), "Constant not found.")
        constToSymbol[constDecl] = symbol
        constToDeclaration[constDecl] = declaration
    }

    override fun definesSymbol(symbol: String) = constToSymbol.inverse().containsKey(symbol)
}

private fun Decl<*>.toSymbol() = GenericSmtLibSymbolTable.encodeSymbol(name)

private fun transformSort(ctx: SMTLIBv2Parser.SortContext): Type {
    val name = ctx.identifier().symbol().text
    return when (name) {
        "Int" -> IntExprs.Int()
        "Bool" -> BoolExprs.Bool()
        "Real" -> RatExprs.Rat()
        "BitVec" -> {
            assert(ctx.identifier().index().size == 1)
            BvExprs.BvType(ctx.identifier().index()[0].text.toInt())
        }

        "Array" -> {
            assert(ctx.sort().size == 2)
            ArrayExprs.Array(transformSort(ctx.sort()[0]), transformSort(ctx.sort()[1]))
        }

        else -> throw UnsupportedOperationException()
    }
}

private fun parseResponse(input: String): PrecisionResponse {
    try {
        val lexer = SMTLIBv2Lexer(CharStreams.fromString(input))
        val parser = SMTLIBv2Parser(CommonTokenStream(lexer))
        lexer.removeErrorListeners()
        lexer.addErrorListener(ThrowExceptionErrorListener())
        parser.removeErrorListeners()
        parser.addErrorListener(ThrowExceptionErrorListener())

        val response = GeneralResponse.fromContext(parser.response())
        if (response.isError) {
            throw SmtLibSolverException(response.reason)
        } else if (!(response.isSpecific && response.asSpecific().isPrecisionResponse)) {
            throw RuntimeException("Unable to parse precision")
        }
        return response.asSpecific().asPrecisionResponse()
    } catch (e: Exception) {
        throw SmtLibSolverException("Could not parse solver output: $input", e)
    }
}