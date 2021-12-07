package hu.bme.mit.theta.analysis;

public interface Lattice<S extends State> extends PartialOrd<S> {

    S top();

    S bottom();

    S meet(S state1, S state2);

    S join(S state1, S state2);

}
