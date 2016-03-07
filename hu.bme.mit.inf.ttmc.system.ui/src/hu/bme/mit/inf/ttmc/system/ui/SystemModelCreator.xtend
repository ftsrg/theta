package hu.bme.mit.inf.ttmc.system.ui

import com.google.common.collect.ImmutableList
import hu.bme.mit.inf.ttmc.constraint.ConstraintManager
import hu.bme.mit.inf.ttmc.constraint.decl.Decl
import hu.bme.mit.inf.ttmc.constraint.expr.Expr
import hu.bme.mit.inf.ttmc.constraint.expr.RefExpr
import hu.bme.mit.inf.ttmc.constraint.type.BoolType
import hu.bme.mit.inf.ttmc.constraint.type.Type
import hu.bme.mit.inf.ttmc.program.decl.VarDecl
import hu.bme.mit.inf.ttmc.program.factory.ProgramFactory
import hu.bme.mit.inf.ttmc.program.sts.STS
import hu.bme.mit.inf.ttmc.program.sts.impl.STSImpl
import hu.bme.mit.inf.ttmc.system.model.InitialConstraintDefinition
import hu.bme.mit.inf.ttmc.system.model.InvariantConstraintDefinition
import hu.bme.mit.inf.ttmc.system.model.PrimedExpression
import hu.bme.mit.inf.ttmc.system.model.SystemDefinition
import hu.bme.mit.inf.ttmc.system.model.SystemSpecification
import hu.bme.mit.inf.ttmc.system.model.TransitionConstraintDefinition
import hu.bme.mit.inf.ttmc.system.model.VariableDeclaration
import java.util.ArrayList
import java.util.Collection
import java.util.HashMap
import java.util.Map

import static com.google.common.base.Preconditions.checkNotNull
import hu.bme.mit.inf.ttmc.constraint.ui.ConstraintModelCreator
import hu.bme.mit.inf.ttmc.program.utils.impl.ProgTypeInferrer

final class SystemModelCreator extends ConstraintModelCreator {
	
	val Map<VariableDeclaration, VarDecl<Type>> localVariableToVar = new HashMap
	
	private val extension ProgramFactory pf
		
	private val SystemSpecification specification
	
	new(ConstraintManager manager, ProgramFactory programFactory, SystemSpecification specification) {
		super(manager, specification)
		this.specification = specification
		this.pf = programFactory
	}
	
	override protected getTypeInferrer(ConstraintManager manager) {
		return new ProgTypeInferrer(manager)
	}
	
	public def SystemModel createSystemModel() {
		val stss = new ArrayList<STS>()
		
		for (propertyDeclaration : specification.propertyDeclarations) {
			stss += create(propertyDeclaration.system as SystemDefinition)
		}
		
		new SystemModelImpl(stss)
	}
	
	private def STS create(SystemDefinition sysDef) {
		localVariableToVar.clear
		val builder = new STSImpl.Builder()
		
		for(constraintDef : sysDef.systemConstraintDefinitions) {
			val expr = constraintDef.expression.toExpr.withType(BoolType)
			if (constraintDef instanceof InitialConstraintDefinition) builder.addInit(expr)
			if (constraintDef instanceof InvariantConstraintDefinition) builder.addInvar(expr)
			if (constraintDef instanceof TransitionConstraintDefinition) builder.addTrans(expr)
		}
		
		for (localVar : localVariableToVar.values) builder.addVar(localVar)
		
		builder.build(manager)
	}
	
	/////
	
	protected def dispatch Decl<Type> toDecl(VariableDeclaration declaration) {
		var varDecl = localVariableToVar.get(declaration)
		if (varDecl === null) {
			val name = declaration.name
			val type = declaration.type.toType
			varDecl = Var(name, type)
			localVariableToVar.put(declaration, varDecl)
		}
		varDecl
	}	
	
	/////
	
	protected def dispatch Expr<? extends Type> toExpr(PrimedExpression expression) {
		val op = expression.operand.toExpr.withType(Type)
		Prime(op)
	}
	
	/////
			
	protected def dispatch RefExpr<? extends Type, ?> toRefExpr(VariableDeclaration declaration) {
		val decl = declaration.toDecl
		val varDecl = decl as VarDecl<Type>
		Ref(varDecl)
	}
	
	/////
	
	private static class SystemModelImpl implements SystemModel {
		
		private val Collection<STS> stss;
		
		private new(Collection<STS> stss) {
			this.stss = ImmutableList.copyOf(checkNotNull(stss))
		}
				
		override getSTSs() {
			stss
		}
		
	}
}