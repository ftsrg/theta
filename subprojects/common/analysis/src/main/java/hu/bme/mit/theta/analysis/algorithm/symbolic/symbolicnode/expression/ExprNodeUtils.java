package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.collections.UniqueTable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNode;

public class ExprNodeUtils {

    public static UniqueTable<MddSymbolicNode> uniqueTable = UniqueTable.newInstance((a, b) -> a.getSymbolicRepresentation().equals(b.getSymbolicRepresentation()), n -> n.getSymbolicRepresentation().hashCode());
}
