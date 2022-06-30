package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.java.mdd.MddSymbolicNode;
import hu.bme.mit.delta.java.mdd.MddVariable;

import java.util.Objects;

public interface IMddSymbolicNode {

    boolean isOn(MddVariable var1);

    boolean isAbove(MddVariable var1);

    boolean isBelow(MddVariable var1);

    default boolean isTerminal() {
        return false;
    }

    void acquire();

    void release();

    int getReferenceCount();

    default <T> Pair<T, MddVariable> getSymbolicRepresentation(Class<T> typeToken) {
        final Pair<Object, MddVariable> symbolicRepresentation = this.getSymbolicRepresentation();
        return new Pair<>(typeToken.cast(symbolicRepresentation.first), symbolicRepresentation.second);
    }

    Pair<Object, MddVariable> getSymbolicRepresentation();

    static boolean equals(MddSymbolicNode obj1, MddSymbolicNode obj2) {
        return !Objects.equals(obj1.getVariable(), obj2.getVariable()) ? false : Objects.equals(obj1.getSymbolicRepresentation(), obj2.getSymbolicRepresentation());
    }

}
