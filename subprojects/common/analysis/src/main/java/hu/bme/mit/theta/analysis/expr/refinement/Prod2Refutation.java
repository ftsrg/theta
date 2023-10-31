package hu.bme.mit.theta.analysis.expr.refinement;

public class Prod2Refutation <R1 extends Refutation, R2 extends Refutation>implements Refutation{

    final private R1 refutation1;
    final private R2 refutation2;

    public Prod2Refutation(R1 refutation1, R2 refutation2) {
        this.refutation1 = refutation1;
        this.refutation2 = refutation2;
    }

    public R1 getRefutation1() {
        return refutation1;
    }

    public R2 getRefutation2() {
        return refutation2;
    }

    @Override
    public int getPruneIndex() {
        if(refutation1.getPruneIndex() < 0) return refutation2.getPruneIndex();
        if(refutation2.getPruneIndex() < 0) return refutation1.getPruneIndex();
        return refutation1.getPruneIndex() > refutation2.getPruneIndex() ? refutation2.getPruneIndex() : refutation1.getPruneIndex();
    }
}
