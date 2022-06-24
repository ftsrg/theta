package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

public interface MddSymbolicNodeTraverser {

    boolean isOn(final MddSymbolicNode node);

    MddSymbolicNode getCurrentNode();

    void moveUp();

    boolean queryChild(int assignment);

    void queryChild();

    void moveDown(int assignment);


}
