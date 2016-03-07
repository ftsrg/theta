package hu.bme.mit.inf.ttmc.program.expr;

import hu.bme.mit.inf.ttmc.constraint.expr.RefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.program.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.program.type.ProcType;

public interface ProcRefExpr<ReturnType extends Type> extends RefExpr<ProcType<ReturnType>, ProcDecl<ReturnType>> {

}
