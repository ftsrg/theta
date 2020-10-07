package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graphfilter.Filter;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class MCM {

    private final Map<String, Filter> definitions;

    private final Set<Constraint> constraints;

    public MCM() {
        constraints = new HashSet<>();
        definitions = new HashMap<>();
    }

    public void addConstraint(Constraint g) {
        constraints.add(g);
    }

    public Set<Constraint> getConstraints() {
        return constraints;
    }

    public void addDefinition(String name, Filter definition) {
        this.definitions.put(name, definition);
    }

    public Map<String, Filter> getDefinitions() {
        return definitions;
    }
}
