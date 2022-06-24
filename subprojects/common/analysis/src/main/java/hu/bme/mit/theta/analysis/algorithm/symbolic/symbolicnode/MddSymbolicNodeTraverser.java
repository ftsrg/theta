package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

public interface MddSymbolicNodeTraverser {

boolean isOn(final MddSymbolicNode node);

    void moveUp();

    boolean queryChild(int assignment);

    void queryChild();

    void moveDown(int assignment);


}
