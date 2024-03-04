package hu.bme.mit.theta.xcfa.analysis.oc

import com.google.common.collect.BiMap
import hu.bme.mit.theta.common.DispatchTable
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.UCSolver
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser
import hu.bme.mit.theta.solver.smtlib.impl.generic.*
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolver
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibExprTransformer
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTypeTransformer
import java.nio.file.Path

internal class OcSolverFactory(solverPath: Path, args: Array<String> = arrayOf("-smt2", "-in"))
    : GenericSmtLibSolverFactory(solverPath, args) {

    override fun createSolver(): Solver = createSolver(false)
    override fun createUCSolver(): UCSolver = createSolver(true)

    private fun createSolver(ucEnabled: Boolean): SmtLibSolver {
        val symbolTable = GenericSmtLibSymbolTable()
        val transformationManager = OcSolverSmtLibTransformationManager(symbolTable)
        val termTransformer = OcSolverSmtLibTermTransformer(symbolTable)
        val solverBinary = GenericSmtLibSolverBinary(solverPath, args)
        return SmtLibSolver(symbolTable, transformationManager, termTransformer, solverBinary, ucEnabled)
    }
}

class OcSolverSmtLibTransformationManager(symbolTable: SmtLibSymbolTable?)
    : GenericSmtLibTransformationManager(symbolTable) {

    override fun instantiateTypeTransformer(transformer: SmtLibTransformationManager): SmtLibTypeTransformer =
        OcSolverSmtLibTypeTransformer(transformer)

    override fun instantiateExprTransformer(transformer: SmtLibTransformationManager): SmtLibExprTransformer =
        OcSolverSmtLibExprTransformer(transformer)
}

internal class OcSolverSmtLibTypeTransformer(transformer: SmtLibTransformationManager)
    : GenericSmtLibTypeTransformer(transformer) {

    override fun buildDispatchTable(builder: DispatchTable.Builder<String>): DispatchTable.Builder<String> =
        super.buildDispatchTable(builder)
            .addCase(OcType::class.java) { "Oc" }
}

internal class OcSolverSmtLibExprTransformer(transformer: SmtLibTransformationManager)
    : GenericSmtLibExprTransformer(transformer) {

    override fun buildDispatchTable(builder: DispatchTable.Builder<String>): DispatchTable.Builder<String> =
        super.buildDispatchTable(builder)
            .addCase(Relation::class.java) {
                val suffix = if ("po" in it.type.toString().lowercase()) "" else toTerm(it.declRef)
                "(oclt-${it.type.toString().lowercase()} ${toTerm(it.from.clk)} ${toTerm(it.to.clk)} $suffix)"
            }
}

internal class OcSolverSmtLibTermTransformer(symbolTable: SmtLibSymbolTable)
    : GenericSmtLibTermTransformer(symbolTable) {

    override fun transformSymbol(ctx: SMTLIBv2Parser.SymbolContext, model: SmtLibModel,
        vars: BiMap<ParamDecl<*>, String>): Expr<*> {
        val value = ctx.text
        if(value.startsWith("Oc!val!")) return OcLitExpr
        return super.transformSymbol(ctx, model, vars)
    }
}
