package hu.bme.mit.theta.xcfa.transformation.grammar.type;

import hu.bme.mit.theta.xcfa.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.xcfa.transformation.model.statements.CStatement;
import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;
import hu.bme.mit.theta.xcfa.transformation.grammar.function.FunctionVisitor;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkState;

public class DeclarationVisitor extends CBaseVisitor<CDeclaration> {
	public static final DeclarationVisitor instance = new DeclarationVisitor();

	/**
	 * From a single declaration context and initialization list this function produces the corresponding CDeclarations
	 * @param declSpecContext declaration context
	 * @param initDeclContext initialization list context
	 * @return the corresponding CDeclarations
	 */
	public List<CDeclaration> getDeclarations(CParser.DeclarationSpecifiersContext declSpecContext, CParser.InitDeclaratorListContext initDeclContext) {
		List<CDeclaration> ret = new ArrayList<>();
		CSimpleType cSimpleType = declSpecContext.accept(TypeVisitor.instance);
		if(cSimpleType.getAssociatedName() != null) {
			CDeclaration cDeclaration = new CDeclaration(cSimpleType.getAssociatedName());
			cDeclaration.setBaseType(cSimpleType.getBaseType());
			cDeclaration.incDerefCounter(cSimpleType.getPointerLevel());
			ret.add(cDeclaration);
		}
		if(initDeclContext != null) {
			for (CParser.InitDeclaratorContext context : initDeclContext.initDeclarator()) {
				CDeclaration declaration = context.declarator().accept(this);
				CStatement initializerExpression;
				if (context.initializer() != null) {
					checkState(context.initializer().initializerList() == null, "Initializer lists not yet implemented!");
					initializerExpression = context.initializer().assignmentExpression().accept(FunctionVisitor.instance);
					declaration.setInitExpr(initializerExpression);
				}
				declaration.setBaseType(cSimpleType.getBaseType());
				ret.add(declaration);
			}
		}
		if(cSimpleType.getAssociatedName() == null && initDeclContext != null && initDeclContext.initDeclarator().size() > 0) {
			ret.get(0).incDerefCounter(cSimpleType.getPointerLevel());
		}
		return ret;
	}

	@Override
	public CDeclaration visitOrdinaryParameterDeclaration(CParser.OrdinaryParameterDeclarationContext ctx) {
		CSimpleType cSimpleType = ctx.declarationSpecifiers().accept(TypeVisitor.instance);
		CDeclaration declaration = ctx.declarator().accept(this);
		declaration.setBaseType(cSimpleType.getBaseType());
		return declaration;
	}

	@Override
	public CDeclaration visitAbstractParameterDeclaration(CParser.AbstractParameterDeclarationContext ctx) {
		CSimpleType cSimpleType = ctx.declarationSpecifiers2().accept(TypeVisitor.instance);
		checkState(ctx.abstractDeclarator() == null, "Abstract declarators not yet supported!");
		return new CDeclaration(cSimpleType);
	}

	@Override
	public CDeclaration visitDeclarator(CParser.DeclaratorContext ctx) {
		checkState(ctx.pointer() == null || ctx.pointer().typeQualifierList().size() == 0, "pointers should not have type qualifiers! (not yet implemented)");
		//checkState(ctx.gccDeclaratorExtension().size() == 0, "Cannot do anything with gccDeclaratorExtensions!");
		CDeclaration decl = ctx.directDeclarator().accept(this);

		if(ctx.pointer() != null) {
			int size = ctx.pointer().stars.size();
			decl.incDerefCounter(size);
		}
		return decl;
	}

	@Override
	public CDeclaration visitDirectDeclaratorId(CParser.DirectDeclaratorIdContext ctx) {
		return new CDeclaration(ctx.getText());
	}

	@Override
	public CDeclaration visitDirectDeclaratorBraces(CParser.DirectDeclaratorBracesContext ctx) {
		return ctx.declarator().accept(this);
	}

	@Override
	public CDeclaration visitDirectDeclaratorArray1(CParser.DirectDeclaratorArray1Context ctx) {
		checkState(ctx.typeQualifierList() == null, "Type qualifiers inside array declarations are not yet implemented.");

		CDeclaration decl = ctx.directDeclarator().accept(this);
		if(ctx.assignmentExpression() != null) {
			decl.addArrayDimension(ctx.assignmentExpression().accept(FunctionVisitor.instance));
		}
		else {
			decl.addArrayDimension(null);
		}
		return decl;
	}

	@Override
	public CDeclaration visitDirectDeclaratorArray2(CParser.DirectDeclaratorArray2Context ctx) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public CDeclaration visitDirectDeclaratorArray3(CParser.DirectDeclaratorArray3Context ctx) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public CDeclaration visitDirectDeclaratorArray4(CParser.DirectDeclaratorArray4Context ctx) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public CDeclaration visitDirectDeclaratorFunctionDecl(CParser.DirectDeclaratorFunctionDeclContext ctx) {
		CDeclaration decl = ctx.directDeclarator().accept(this);
		checkState(ctx.parameterTypeList() == null || ctx.parameterTypeList().ellipses == null, "Variable args are not yet supported!");
		if(ctx.parameterTypeList() != null) {
			for (CParser.ParameterDeclarationContext parameterDeclarationContext : ctx.parameterTypeList().parameterList().parameterDeclaration()) {
				decl.addFunctionParam(parameterDeclarationContext.accept(this));
			}
		}
		decl.setFunc(true);
		return decl;
	}

	@Override
	public CDeclaration visitDirectDeclaratorBitField(CParser.DirectDeclaratorBitFieldContext ctx) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}
}
