package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.UniqueTable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNode;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class ExpressionNodeUtils {

    public static UniqueTable<MddSymbolicNode> uniqueTable = UniqueTable.newInstance((a, b) -> a.getSymbolicRepresentation().equals(b.getSymbolicRepresentation()), n -> n.getSymbolicRepresentation().hashCode());

    public static MddSymbolicNode  terminalOne = new MddSymbolicNode(new Pair<>(True(), null),null);

}
