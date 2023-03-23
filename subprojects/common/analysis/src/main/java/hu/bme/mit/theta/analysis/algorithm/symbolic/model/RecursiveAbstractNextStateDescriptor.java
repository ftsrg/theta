package hu.bme.mit.theta.analysis.algorithm.symbolic.model;

public interface RecursiveAbstractNextStateDescriptor extends AbstractNextStateDescriptor{

    interface Cursor {

        Cursor valueCursor(int from);

    }

    Cursor cursor(int from);

}
