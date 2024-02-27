package hu.bme.mit.theta.sts.analysis;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

import java.util.ArrayList;




public class Frame {
    private final Frame parent;
    private final ArrayList<Expr<BoolType>> exprs;

    private final Solver solver;

    Frame(final Frame parent, Solver solver) {
        this.parent = parent;
        this.solver = solver;
        exprs = new ArrayList<>();
    }
    void add(Expr<BoolType> e){
        exprs.add(e);
    }
}
