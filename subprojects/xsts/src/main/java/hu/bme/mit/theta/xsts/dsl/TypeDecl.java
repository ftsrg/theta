package hu.bme.mit.theta.xsts.dsl;

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;

import static com.google.common.base.Preconditions.checkArgument;

public final class TypeDecl {

    private final String name;
    private final List<String> literals;
    private final List<BigInteger> intValues;

    private TypeDecl(final String name, final List<String> literals, final List<BigInteger> intValues) {
        this.name = name;
        checkArgument(literals.size()==intValues.size());
        this.literals = literals;
        this.intValues = intValues;
    }

    public static TypeDecl of(final String name, final List<String> literals, final List<BigInteger> intValues){
        return new TypeDecl(name, literals, intValues);
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

    public List<BigInteger> getIntValues() { return intValues; }

    @Override
    public String toString() {
        return name+" "+literals;
    }
}
