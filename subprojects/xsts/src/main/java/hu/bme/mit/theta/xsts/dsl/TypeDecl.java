package hu.bme.mit.theta.xsts.dsl;

import java.util.List;

public class TypeDecl {

    private String name;
    private List<String> literals;

    public TypeDecl(String name, List<String> literals) {
        this.name = name;
        this.literals = literals;
    }

    public String getName() {
        return name;
    }

    public List<String> getLiterals() {
        return literals;
    }

    @Override
    public String toString() {
        return name+" "+literals;
    }
}
