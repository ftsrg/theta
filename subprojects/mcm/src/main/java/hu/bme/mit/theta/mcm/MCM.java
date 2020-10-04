package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graphfilter.Filter;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class MCM<T extends MemoryAccess> {

    private final Map<String, Filter<T>> definitions;

    private final Set<Constraint<T>> constraints;

    public MCM() {
        constraints = new HashSet<>();
        definitions = new HashMap<>();
    }

    public void addConstraint(Constraint<T> g) {
        constraints.add(g);
    }

    public Set<Constraint<T>> getConstraints() {
        return constraints;
    }

    public void addDefinition(String name, Filter<T> definition) {
        this.definitions.put(name, definition);
    }

    public Map<String, Filter<T>> getDefinitions() {
        return definitions;
    }
}
