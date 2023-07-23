package hu.bme.mit.theta.frontend.visitor

import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2BaseVisitor
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import hu.bme.mit.theta.frontend.model.Btor2Node

class OperationVisitor : Btor2BaseVisitor<Btor2Node>() {
    override fun visitOpidx(ctx: Btor2Parser.OpidxContext): Btor2Node {
        // Implementation for visiting opidx rule
        throw NotImplementedError()
    }

    override fun visitExt(ctx: Btor2Parser.ExtContext): Btor2Node {
        // Implementation for visiting ext rule
        throw NotImplementedError()
    }

    override fun visitSlice(ctx: Btor2Parser.SliceContext): Btor2Node {
        // Implementation for visiting slice rule
        throw NotImplementedError()
    }

    override fun visitOp(ctx: Btor2Parser.OpContext): Btor2Node {
        // Implementation for visiting op rule
        throw NotImplementedError()
    }

    override fun visitBinop(ctx: Btor2Parser.BinopContext): Btor2Node {
        // Implementation for visiting binop rule
        throw NotImplementedError()
    }

    override fun visitUnop(ctx: Btor2Parser.UnopContext): Btor2Node {
        // Implementation for visiting unop rule
        throw NotImplementedError()
    }

    override fun visitTerop(ctx: Btor2Parser.TeropContext): Btor2Node {
        // Implementation for visiting terop rule
        throw NotImplementedError()
    }

}