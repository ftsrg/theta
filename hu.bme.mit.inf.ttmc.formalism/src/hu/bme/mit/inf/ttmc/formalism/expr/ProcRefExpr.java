package hu.bme.mit.inf.ttmc.formalism.expr;

import hu.bme.mit.inf.ttmc.constraint.expr.RefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.type.ProcType;

public interface ProcRefExpr<ReturnType extends Type> extends RefExpr<ProcType<ReturnType>, ProcDecl<ReturnType>> {

}
