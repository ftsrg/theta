package hu.bme.mit.theta.analysis.algorithm.symbolic.model;

import java.io.Closeable;

public interface RecursiveAbstractNextStateDescriptor extends AbstractNextStateDescriptor{

    interface Cursor extends Closeable {

        int key();

        RecursiveAbstractNextStateDescriptor value();

        boolean moveNext();

        Cursor valueCursor(int from);

        void close();
    }

    Cursor cursor(int from);

}
