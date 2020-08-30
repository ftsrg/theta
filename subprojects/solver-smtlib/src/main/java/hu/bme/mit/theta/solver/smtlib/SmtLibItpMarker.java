package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public abstract class SmtLibItpMarker<T> implements ItpMarker {
    private final Stack<T> terms;

    public SmtLibItpMarker() {
        terms = new StackImpl<>();
    }

    public void add(final T term) {
        terms.add(checkNotNull(term));
    }

    public void push() {
        terms.push();
    }

    public void pop(final int n) {
        terms.pop(n);
    }

    public Collection<T> getTerms() {
        return terms.toCollection();
    }
}
