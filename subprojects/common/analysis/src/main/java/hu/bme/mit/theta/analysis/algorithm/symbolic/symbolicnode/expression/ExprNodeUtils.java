package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.collections.UniqueTable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNode;

/**
 * Temporary class that will be deleted once the issues concerning the unique table are resolved
 */
public class ExprNodeUtils {

    public static UniqueTable<MddSymbolicNode> uniqueTable = UniqueTable.newInstance((a, b) -> a.getSymbolicRepresentation().equals(b.getSymbolicRepresentation()), n -> n.getSymbolicRepresentation().hashCode());
}
