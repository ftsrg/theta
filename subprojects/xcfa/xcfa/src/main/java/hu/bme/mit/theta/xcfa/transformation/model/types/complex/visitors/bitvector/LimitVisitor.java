package hu.bme.mit.theta.xcfa.transformation.model.types.complex.visitors.bitvector;

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;

public class LimitVisitor extends CComplexType.CComplexTypeVisitor<Expr<BvType>, AssumeStmt> {

}
