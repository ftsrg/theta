package hu.bme.mit.theta.xcfa.analysis.timed

import hu.bme.mit.theta.analysis.algorithm.lazy.lu.LuZonePre
import hu.bme.mit.theta.analysis.zone.BoundFunc
import hu.bme.mit.theta.core.clock.op.GuardOp
import hu.bme.mit.theta.core.clock.op.ResetOp
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.model.ClockDelayLabel
import hu.bme.mit.theta.xcfa.model.ClockOpLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

class XcfaLuZonePre : LuZonePre<XcfaAction> {

  override fun pre(boundFunc: BoundFunc, action: XcfaAction): BoundFunc {
    val preBoundsBuilder = boundFunc.transform()
    action.label.getFlatLabels().reversed().forEach { label ->
      when (label) {
        is ClockDelayLabel -> {} // do nothing
        is ClockOpLabel -> label.op.let { op ->
          when (op) {
            is GuardOp -> preBoundsBuilder.add(op.constr)
            is ResetOp -> preBoundsBuilder.remove(op.`var`)
            else -> error("Unexpected clock op: $op")
          }
        }
        else -> error("Unexpected label $label")
      }
    }
    return preBoundsBuilder.build()
  }
}
