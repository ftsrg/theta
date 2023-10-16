package hu.bme.mit.theta.analysis.algorithm;

import com.google.errorprone.annotations.Var;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.solver.SolverFactory;

public interface MonolithicTransFunc {
    Expr<BoolType> getTransExpr();

    Expr<BoolType> getInitExpr();

    Expr<BoolType> getPropExpr();

    VarIndexing getInitIndexing();

    VarIndexing getOffsetIndexing();


}
