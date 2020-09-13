package hu.bme.mit.theta.mcm;

import java.util.ArrayList;
import java.util.List;
import java.util.function.UnaryOperator;

public class EdgeDB {
    public static EdgeDB empty() {
        return new EdgeDB();
    }

    public EdgeDB filterNext(String edgeLabel, UnaryOperator<EdgeDB> lhs, UnaryOperator<EdgeDB> rhs) {
        return this;
    }

    public EdgeDB filterSuccessors(String edgeLabel, UnaryOperator<EdgeDB> lhs, UnaryOperator<EdgeDB> rhs) {
        return this;
    }

    public List<?> getVars() {
        return new ArrayList<>();
    }

    public List<?> getThreads() {
        return new ArrayList<>();
    }

    public List<?> getNodes() {
        return new ArrayList<>();
    }

    public EdgeDB union(EdgeDB apply) {
        return this;
    }

    public EdgeDB intersect(EdgeDB apply) {
        return this;
    }

    public EdgeDB minus(EdgeDB apply) {
        return this;
    }

    public EdgeDB multiply(EdgeDB apply) {
        return this;
    }

    public EdgeDB multiplyLater(EdgeDB apply) {
        return this;
    }

    public EdgeDB filterNamed(String text) {
        return this;
    }

    public EdgeDB filterTagged(String text) {
        return this;
    }

    public EdgeDB and(EdgeDB apply) {
        return this;
    }

    public EdgeDB or(EdgeDB apply) {
        return this;
    }

    public EdgeDB not() {
        return this;
    }

    public EdgeDB imply(EdgeDB apply) {
        return this;
    }

    public EdgeDB isAcyclic() {
        return this;
    }

    public EdgeDB isIrreflexive() {
        return this;
    }

    public EdgeDB isEmpty() {
        return this;
    }

    public boolean isOk() {
        return true;
    }

}
