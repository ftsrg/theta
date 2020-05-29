package hu.bme.mit.theta.xsts.dsl;

import java.util.List;
import java.util.Objects;

public class TypeDecl {

    private String name;
    private List<String> literals;

    public TypeDecl(String name, List<String> literals) {
        this.name = name;
        this.literals = literals;
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof TypeDecl) {
            final TypeDecl that = (TypeDecl) obj;
            return this.name.equals(that.name);
        } else {
            return false;
        }
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
