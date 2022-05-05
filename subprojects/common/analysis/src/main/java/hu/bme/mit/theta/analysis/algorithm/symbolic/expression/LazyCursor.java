package hu.bme.mit.theta.analysis.algorithm.symbolic.expression;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.java.mdd.MddSymbolicNode;
import hu.bme.mit.theta.core.type.LitExpr;

import java.util.Optional;

public class LazyCursor<T extends MddSymbolicNode> implements IntObjCursor<T> {

    private final AssignmentEnumerator enumerator;
    private int currentIndex;
    private int currentKey;

    public LazyCursor(AssignmentEnumerator enumerator) {
        this.enumerator = enumerator;
        this.currentIndex = 0;
    }

    @Override
    public int key() {
        return currentKey;
    }

    @Override
    public T value() {
        // request new ExpressionNode from somewhere using the key
        return null;
    }

    @Override
    public boolean moveNext() {
        Optional<LitExpr<?>> optional = enumerator.get(currentIndex++);
        if(optional.isPresent()){
            currentKey = LitExprConverter.toInt(optional.get());
            return true;
        } else {
            return false;
        }
    }
}
