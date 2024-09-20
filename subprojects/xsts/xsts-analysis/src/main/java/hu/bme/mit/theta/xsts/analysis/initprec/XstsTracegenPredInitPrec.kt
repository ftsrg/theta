package hu.bme.mit.theta.xsts.analysis.initprec

import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.prod2.Prod2Prec
import hu.bme.mit.theta.core.utils.StmtAtomCollector
import hu.bme.mit.theta.xsts.XSTS

class XstsTracegenPredInitPrec : XstsInitPrec{
    override fun createExpl(xsts: XSTS?): ExplPrec {
        throw RuntimeException("Explicit precision is not supported with guard init precision")
    }

    override fun createPred(xsts: XSTS): PredPrec {
        val tran = xsts.tran
        val ctrlVars = xsts.ctrlVars // TODO add to pred

        val assumes = StmtAtomCollector.collectAtoms(tran)
        //val assumes = StmtAssumeCollector.collectAssumes(tran)
        return PredPrec.of(assumes)
    }

    override fun createProd2ExplPred(xsts: XSTS): Prod2Prec<ExplPrec, PredPrec> {
        throw RuntimeException("Prod2ExplPred precision is not supported with variable list precision")
    }
}