package hu.bme.mit.inf.ttmc.constraint.ui

import com.google.common.collect.ImmutableList
import hu.bme.mit.inf.ttmc.constraint.ConstraintManager
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl
import hu.bme.mit.inf.ttmc.constraint.decl.Decl
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl
import hu.bme.mit.inf.ttmc.constraint.expr.Expr
import hu.bme.mit.inf.ttmc.constraint.expr.RefExpr
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory
import hu.bme.mit.inf.ttmc.constraint.model.ConstantDeclaration
import hu.bme.mit.inf.ttmc.constraint.model.ConstraintSpecification
import hu.bme.mit.inf.ttmc.constraint.model.Declaration
import hu.bme.mit.inf.ttmc.constraint.model.FunctionDeclaration
import hu.bme.mit.inf.ttmc.constraint.model.ParameterDeclaration
import hu.bme.mit.inf.ttmc.constraint.model.ReferenceExpression
import hu.bme.mit.inf.ttmc.constraint.type.BoolType
import hu.bme.mit.inf.ttmc.constraint.type.Type
import java.util.ArrayList
import java.util.Collection
import java.util.HashMap
import java.util.Map

import static com.google.common.base.Preconditions.checkNotNull

public class ConstraintModelCreator extends ExprCreator {
	
	private val extension DeclFactory df
	
	private val Map<ConstantDeclaration, ConstDecl<Type>> constantToConst
	private val Map<ParameterDeclaration, ParamDecl<Type>> parameterToParam
	
	private val ConstraintSpecification specification;

	new(ConstraintManager manager, ConstraintSpecification specification) {
		super(manager)
		checkNotNull(specification)
		
		this.specification = specification
		
		df = manager.declFactory
		
		constantToConst = new HashMap
		parameterToParam = new HashMap
	}
	
	public def ConstraintModel create() {
		val constraints = new ArrayList<Expr<? extends BoolType>>
		for (basicConstraintDefinition : specification.basicConstraintDefinitions) {
			val expression = basicConstraintDefinition.expression
			val expr = expression.toExpr.withType(BoolType)
			constraints += expr
		}
		val constDecls = constantToConst.values

		val model = new ConstraintModelImpl(constDecls, constraints)
		
		model
	}
	
	////////////////////////////////////////////////////////////////////////////////////////////
	
	protected def dispatch Expr<? extends Type> toExpr(ReferenceExpression expression) {
		expression.declaration.toRefExpr
	}
	
	////
	
	protected def dispatch RefExpr<? extends Type, ?> toRefExpr(Declaration declaration) {
		throw new UnsupportedOperationException("Not supported")
	}
	
	protected def dispatch RefExpr<? extends Type, ?> toRefExpr(ConstantDeclaration declaration) {
		val decl = declaration.toDecl
		val constDecl = decl as ConstDecl<Type>
		Ref(constDecl)
	}
	
	protected def dispatch RefExpr<? extends Type, ?> toRefExpr(ParameterDeclaration declaration) {
		val decl = declaration.toDecl
		val paramDecl = decl as ParamDecl<Type>
		Ref(paramDecl)
	}
	
	/////////////////////////////////////////////////////////////////////
	
	protected def dispatch Decl<Type> toDecl(Declaration declaration) {
		throw new UnsupportedOperationException("Not supported: " + declaration.class)
	}
	
	protected def dispatch Decl<Type> toDecl(ConstantDeclaration declaration) {
		var constDecl = constantToConst.get(declaration)
		if (constDecl === null) {
			val name = declaration.name
			val type = declaration.type.toType
			constDecl = Const(name, type)
			constantToConst.put(declaration, constDecl)
		}
		constDecl
	}
	
	protected def dispatch Decl<Type> toDecl(FunctionDeclaration declaration) {
		throw new UnsupportedOperationException("TODO")
	}
	
	protected def dispatch Decl<Type> toDecl(ParameterDeclaration declaration) {
		var paramDecl = parameterToParam.get(declaration)
		if (paramDecl === null) {
			val name = declaration.name
			val type = declaration.type.toType
			paramDecl = Param(name, type)
			parameterToParam.put(declaration, paramDecl)
		}
		return paramDecl
	}
	
	//////////////////////////////////////////////////////////////////////
	
	private static class ConstraintModelImpl implements ConstraintModel {
		private val Collection<ConstDecl<? extends Type>> constDecls
		private val Collection<Expr<? extends BoolType>> constraints

		private new(Collection<? extends ConstDecl<? extends Type>> constDecls, Collection<? extends Expr<? extends BoolType>> constraints) {
			this.constDecls = ImmutableList.copyOf(checkNotNull(constDecls));
			this.constraints = ImmutableList.copyOf(checkNotNull(constraints));
		}
	
		override Collection<ConstDecl<? extends Type>> getConstDecls() {
			 constDecls
		}
	
		override Collection<Expr<? extends BoolType>> getConstraints() {
			constraints
		}
	}

}
