package hu.bme.mit.theta.analysis.algorithm.symbolic.expression;

import com.google.common.base.Supplier;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.solver.Solver;

public class ExpressionVariable {

    public static <T> IntObjMapView<MddSymbolicNode> getNodeInterpreter(MddSymbolicNode node, MddVariable variable, Supplier<Solver> solverSupplier) {
        if (!node.isOn(variable)) {
            if (!node.isBelow(variable)) {
                throw new AssertionError();
            }

            IntObjMapView<MddSymbolicNode> nodeInterpreter = IntObjMapView.empty(node);
            if (variable.isBounded()) {
                nodeInterpreter = ((IntObjMapView)nodeInterpreter).trim(IntSetView.range(0, variable.getDomainSize()));
            }
            return nodeInterpreter;
        }

        if(node.isComplete()){
            return node.getCacheView();
        } else {
            return new IncompleteMddSymbolicNodeInterpretation(node, new ExpressionNodeTraverser(node, solverSupplier));
        }
    }


}
