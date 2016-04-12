package hu.bme.mit.inf.ttmc.formalism.common.expr;

import hu.bme.mit.inf.ttmc.core.expr.RefExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;

public interface ProcRefExpr<ReturnType extends Type> extends RefExpr<ProcType<ReturnType>, ProcDecl<ReturnType>> {

}
