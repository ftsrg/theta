package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import com.google.common.base.Supplier;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.IncompleteMddSymbolicNodeInterpretation;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNode;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeTraverser;
import hu.bme.mit.theta.solver.Solver;

public class ExpressionVariable {

    public static IntObjMapView<MddSymbolicNode> getNodeInterpreter(MddSymbolicNode node, MddVariable variable, Supplier<Solver> solverSupplier) {
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
            return new IncompleteMddSymbolicNodeInterpretation(node, getNodeTraverser(node, solverSupplier));
        }
    }

    public static MddSymbolicNodeTraverser getNodeTraverser(MddSymbolicNode node, Supplier<Solver> solverSupplier){
        return new ExpressionNodeTraverser(node, solverSupplier);
    }


}
