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
package hu.bme.mit.theta.frontend.promela.grammar

import hu.bme.mit.theta.frontend.promela.model.Statement
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaBaseVisitor
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaParser

class StatementVisitor : promelaBaseVisitor<Statement>() {
    override fun visitIfStmnt(ctx: promelaParser.IfStmntContext?): Statement {
        return super.visitIfStmnt(ctx)
    }

    override fun visitDoStmnt(ctx: promelaParser.DoStmntContext?): Statement {
        return super.visitDoStmnt(ctx)
    }

    override fun visitForStmnt(ctx: promelaParser.ForStmntContext?): Statement {
        return super.visitForStmnt(ctx)
    }

    override fun visitAtomicStmnt(ctx: promelaParser.AtomicStmntContext?): Statement {
        return super.visitAtomicStmnt(ctx)
    }

    override fun visitDstepStmnt(ctx: promelaParser.DstepStmntContext?): Statement {
        return super.visitDstepStmnt(ctx)
    }

    override fun visitSelectStmnt(ctx: promelaParser.SelectStmntContext?): Statement {
        return super.visitSelectStmnt(ctx)
    }

    override fun visitSequenceStmnt(ctx: promelaParser.SequenceStmntContext?): Statement {
        return super.visitSequenceStmnt(ctx)
    }

    override fun visitSendStmnt(ctx: promelaParser.SendStmntContext?): Statement {
        return super.visitSendStmnt(ctx)
    }

    override fun visitReceiveStmnt(ctx: promelaParser.ReceiveStmntContext?): Statement {
        return super.visitReceiveStmnt(ctx)
    }

    override fun visitAssignStmnt(ctx: promelaParser.AssignStmntContext?): Statement {
        return super.visitAssignStmnt(ctx)
    }

    override fun visitElseStmnt(ctx: promelaParser.ElseStmntContext?): Statement {
        return super.visitElseStmnt(ctx)
    }

    override fun visitBreakStmnt(ctx: promelaParser.BreakStmntContext?): Statement {
        return super.visitBreakStmnt(ctx)
    }

    override fun visitGotoStmnt(ctx: promelaParser.GotoStmntContext?): Statement {
        return super.visitGotoStmnt(ctx)
    }

    override fun visitNameStmnt(ctx: promelaParser.NameStmntContext?): Statement {
        return super.visitNameStmnt(ctx)
    }

    override fun visitPrintStmnt(ctx: promelaParser.PrintStmntContext?): Statement {
        return super.visitPrintStmnt(ctx)
    }

    override fun visitAssertStmnt(ctx: promelaParser.AssertStmntContext?): Statement {
        return super.visitAssertStmnt(ctx)
    }

    override fun visitExprStmnt(ctx: promelaParser.ExprStmntContext?): Statement {
        return super.visitExprStmnt(ctx)
    }
}
