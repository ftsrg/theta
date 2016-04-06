package hu.bme.mit.inf.ttmc.formalism.program.factory;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public interface ProgramDeclFactory extends VarDeclFactory {

	public <R extends Type> ProcDecl<R> Proc(final String name, List<? extends ParamDecl<? extends Type>> paramDecls,
			final R returnType);

	public <R extends Type> ProcDecl<R> Proc(final String name, List<? extends ParamDecl<? extends Type>> paramDecls,
			final R returnType, final Stmt def);

}
