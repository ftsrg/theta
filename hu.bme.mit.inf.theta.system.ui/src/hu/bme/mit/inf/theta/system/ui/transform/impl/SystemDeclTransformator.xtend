package hu.bme.mit.inf.theta.system.ui.transform.impl

import hu.bme.mit.inf.theta.core.type.Type
import hu.bme.mit.inf.theta.constraint.ui.transform.TypeTransformator
import hu.bme.mit.inf.theta.constraint.ui.transform.impl.ConstraintDeclTransformator
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl
import hu.bme.mit.inf.theta.system.model.VariableDeclaration
import java.util.HashMap
import java.util.Map

import static hu.bme.mit.inf.theta.formalism.common.decl.impl.Decls2.*;

public class SystemDeclTransformator extends ConstraintDeclTransformator {

	private val Map<VariableDeclaration, VarDecl<Type>> variableToVar
	
	private val extension TypeTransformator tt
	
	public new(SystemTransformationManager manager) {
		super(manager)
		tt = manager.typeTransformator
		variableToVar = new HashMap
	}
	
	////
	
	protected def dispatch VarDecl<Type> toDecl(VariableDeclaration declaration) {
		var varDecl = variableToVar.get(declaration)
		if (varDecl === null) {
			val name = declaration.name
			val type = declaration.type.transform
			varDecl = Var(name, type)
			variableToVar.put(declaration, varDecl)
		}
		varDecl
	}
	
}