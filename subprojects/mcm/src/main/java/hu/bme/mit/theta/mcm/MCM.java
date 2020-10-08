package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashSet;
import java.util.Set;

public class MCM {
    private boolean violated;

    private final Set<Constraint> constraints;
    private Constraint violator;

    public MCM() {
        constraints = new HashSet<>();
    }

    public MCM(boolean violated, Set<Constraint> constraints, Constraint violator) {
        this.violated = violated;
        this.constraints = new HashSet<>();
        for (Constraint constraint : constraints) {
            Constraint duplicated = constraint.duplicate();
            this.constraints.add(duplicated);
            if(violator == constraint) this.violator = duplicated;
        }
    }

    public void addConstraint(Constraint g) {
        constraints.add(g);
    }

    public Set<Constraint> getConstraints() {
        return constraints;
    }

    public void checkMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        for (Constraint constraint : constraints) {
            if(!constraint.checkMk(source, target, label, isFinal)) {
                violated = true;
                violator = constraint;
                return;
            }
        }
        violated = false;
    }

    public void checkRm(MemoryAccess source, MemoryAccess target, String label) {
        for (Constraint constraint : constraints) {
            if(!constraint.checkRm(source, target, label)) {
                violated = true;
                return;
            }
        }
        violated = false;
    }

    public boolean isViolated() {
        return violated;
    }

    public MCM duplicate() {
        return new MCM(violated, constraints, violator);
    }

    public Constraint getViolator() {
        return violator;
    }
}
