package hu.bme.mit.inf.theta.benchmark.bmc;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.impl.ExprRewriterVisitor;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.theta.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.theta.formalism.utils.FailStmtVisitor;

public class StmtToExprVisitor extends FailStmtVisitor<IndexMap, List<Expr<? extends BoolType>>> {


}
