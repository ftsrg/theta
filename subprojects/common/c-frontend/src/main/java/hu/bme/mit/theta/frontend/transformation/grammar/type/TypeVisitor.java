package hu.bme.mit.theta.frontend.transformation.grammar.type;

import hu.bme.mit.theta.c.frontend.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.Enum;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.NamedType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.Struct;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory.Atomic;
import static hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory.DeclaredName;
import static hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory.Enum;
import static hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory.Extern;
import static hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory.NamedType;
import static hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory.Signed;
import static hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory.Typedef;
import static hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory.Unsigned;
import static hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory.Volatile;
import static hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory.ThreadLocal;

public class TypeVisitor extends CBaseVisitor<CSimpleType> {
	public static final TypeVisitor instance = new TypeVisitor();
	private TypeVisitor(){}

	private static final List<String> standardTypes =
			List.of("int", "char", "long", "short", "void", "float", "double", "unsigned", "_Bool");
	private static final List<String> shorthandTypes =
			List.of("long", "short", "unsigned", "_Bool");


	@Override
	public CSimpleType visitDeclarationSpecifiers(CParser.DeclarationSpecifiersContext ctx) {
		return createCType(ctx.declarationSpecifier());
	}

	@Override
	public CSimpleType visitDeclarationSpecifiers2(CParser.DeclarationSpecifiers2Context ctx) {
		return createCType(ctx.declarationSpecifier());
	}


	private CSimpleType mergeCTypes(List<CSimpleType> cSimpleTypes) {
		List<CSimpleType> enums = cSimpleTypes.stream().filter(cType -> cType instanceof Enum).collect(Collectors.toList());
		if(enums.size() > 0) {
			System.err.println("WARNING: enums are not yet supported! Using int instead.");
			cSimpleTypes.add(NamedType("int"));
			cSimpleTypes.removeAll(enums);
		}
		List<CSimpleType> namedElements = cSimpleTypes.stream().filter(cType -> cType instanceof NamedType).collect(Collectors.toList());
		if(namedElements.size() == 0) namedElements.add(NamedType("int"));
		NamedType mainType = (NamedType) namedElements.get(namedElements.size() - 1);
		if (shorthandTypes.contains(mainType.getNamedType())) {
			mainType = NamedType("int");
		} else {
			cSimpleTypes.remove(mainType);
		}

		CSimpleType type = mainType.apply(cSimpleTypes);
		// we didn't get explicit signedness
		if (type.isSigned() == null) {
			if (type instanceof NamedType && ((NamedType) type).getNamedType().contains("char")) {
				System.err.println("WARNING: signedness of the type char is implementation specific. Right now it is interpreted as a signed char.");
			}
			type.setSigned(true);
		}
		return type;
	}

	@Override
	public CSimpleType visitSpecifierQualifierList(CParser.SpecifierQualifierListContext ctx) {
		return createCType(ctx);
	}

	private CSimpleType createCType(CParser.SpecifierQualifierListContext specifierQualifierListContext) {
		List<CSimpleType> cSimpleTypes = new ArrayList<>();
		if(specifierQualifierListContext != null) {
			for (CParser.TypeSpecifierOrQualifierContext typeSpecifierOrQualifierContext : specifierQualifierListContext.typeSpecifierOrQualifier()) {
				CSimpleType qualifierSpecifier = null;
				if(typeSpecifierOrQualifierContext.typeSpecifier() != null) {
					qualifierSpecifier = typeSpecifierOrQualifierContext.typeSpecifier().accept(this);
				}
				else if(typeSpecifierOrQualifierContext.typeQualifier() != null) {
					qualifierSpecifier = typeSpecifierOrQualifierContext.typeQualifier().accept(this);
				}
				if(qualifierSpecifier != null) cSimpleTypes.add(qualifierSpecifier);
			}
			if(specifierQualifierListContext.typeSpecifierPointer() != null) {
				CSimpleType qualifierSpecifier = specifierQualifierListContext.typeSpecifierPointer().accept(this);
				if(qualifierSpecifier != null) cSimpleTypes.add(qualifierSpecifier);
			}
		}

		return mergeCTypes(cSimpleTypes);
	}

	private CSimpleType createCType(List<CParser.DeclarationSpecifierContext> declarationSpecifierContexts) {
		List<CSimpleType> cSimpleTypes = new ArrayList<>();
		for (CParser.DeclarationSpecifierContext declarationSpecifierContext : declarationSpecifierContexts) {
			CSimpleType ctype = declarationSpecifierContext.accept(this);
			if(ctype != null) cSimpleTypes.add(ctype);
		}

		return mergeCTypes(cSimpleTypes);
	}

	@Override
	public CSimpleType visitStorageClassSpecifier(CParser.StorageClassSpecifierContext ctx) {
		switch(ctx.getText()) {
			case "typedef": return Typedef();
			case "extern": return Extern();
			case "static": return null;
			case "auto":
			case "register":
			case "_Thread_local": throw new UnsupportedOperationException("Not yet implemented");
		}
		throw new UnsupportedOperationException("Storage class specifier not expected: " + ctx.getText());
	}

	@Override
	public CSimpleType visitTypeSpecifierAtomic(CParser.TypeSpecifierAtomicContext ctx) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public CSimpleType visitTypeSpecifierCompound(CParser.TypeSpecifierCompoundContext ctx) {
		return ctx.structOrUnionSpecifier().accept(this);
	}

	@Override
	public CSimpleType visitCompoundDefinition(CParser.CompoundDefinitionContext ctx) {
		if(ctx.structOrUnion().Struct() != null) {
			String name = null;
			if(ctx.Identifier()!=null) name = ctx.Identifier().getText();
			Struct struct = CSimpleTypeFactory.Struct(name);
			for (CParser.StructDeclarationContext structDeclarationContext : ctx.structDeclarationList().structDeclaration()) {
				CParser.SpecifierQualifierListContext specifierQualifierListContext = structDeclarationContext.specifierQualifierList();
				CSimpleType cSimpleType = specifierQualifierListContext.accept(this);
				if (structDeclarationContext.structDeclaratorList() == null) {
					struct.addField(cSimpleType.getAssociatedName(), cSimpleType);
				} else {
					for (CParser.StructDeclaratorContext structDeclaratorContext : structDeclarationContext.structDeclaratorList().structDeclarator()) {
						CDeclaration declaration = structDeclaratorContext.accept(DeclarationVisitor.instance);
						struct.addField(declaration.getName(), cSimpleType);
					}
				}
			}
			return struct;
		} else {
			System.err.println("Warning: CompoundDefinitions are not yet implemented!");
			return NamedType("int");
		}
	}

	@Override
	public CSimpleType visitCompoundUsage(CParser.CompoundUsageContext ctx) {
		String text = ctx.Identifier().getText();
		if (ctx.structOrUnion().Struct() != null) return Struct.getByName(text);
		else return NamedType(ctx.structOrUnion().getText() + " " + text);
	}

	@Override
	public CSimpleType visitTypeSpecifierEnum(CParser.TypeSpecifierEnumContext ctx) {
		return ctx.enumSpecifier().accept(this);
	}

	@Override
	public CSimpleType visitEnumDefinition(CParser.EnumDefinitionContext ctx) {
		String id = ctx.Identifier() == null ? null : ctx.Identifier().getText();
		Map<String, Optional<Expr<?>>> fields = new LinkedHashMap<>();
		for (CParser.EnumeratorContext enumeratorContext : ctx.enumeratorList().enumerator()) {
			String value = enumeratorContext.enumerationConstant().getText();
			CParser.ConstantExpressionContext expressionContext = enumeratorContext.constantExpression();
			Expr<?> expr = expressionContext == null ? null : null;//expressionContext.accept(null ); // TODO
			fields.put(value, Optional.ofNullable(expr));
		}
		return Enum(id, fields);
	}

	@Override
	public CSimpleType visitEnumUsage(CParser.EnumUsageContext ctx) {
		return NamedType("enum " + ctx.Identifier().getText());
	}

	@Override
	public CSimpleType visitTypeSpecifierExtension(CParser.TypeSpecifierExtensionContext ctx) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public CSimpleType visitTypeSpecifierPointer(CParser.TypeSpecifierPointerContext ctx) {
		CSimpleType subtype = ctx.typeSpecifier().accept(this);
		if(subtype == null) return null;
		for (Token star : ctx.pointer().stars) {
			subtype.incrementPointer();
		}
		return subtype;
	}

	@Override
	public CSimpleType visitTypeSpecifierSimple(CParser.TypeSpecifierSimpleContext ctx) {
		switch (ctx.getText()) {
			case "signed":
				return Signed();
			case "unsigned":
				return Unsigned();
			case "_Bool":
				return NamedType("_Bool");
			default:
				return NamedType(ctx.getText());
		}
	}

	@Override
	public CSimpleType visitTypeSpecifierGccThread(CParser.TypeSpecifierGccThreadContext ctx) {
		return ThreadLocal();
	}

	@Override
	public CSimpleType visitTypeSpecifierFloat(CParser.TypeSpecifierFloatContext ctx) {
		return NamedType("float");
	}

	@Override
	public CSimpleType visitTypeSpecifierDouble(CParser.TypeSpecifierDoubleContext ctx) {
		return NamedType("double");
	}

	@Override
	public CSimpleType visitTypeSpecifierTypedefName(CParser.TypeSpecifierTypedefNameContext ctx) {
		Optional<CComplexType> type = TypedefVisitor.instance.getType(ctx.getText());
		if(type.isPresent()) {
			CSimpleType origin = type.get().getOrigin().copyOf();
			origin.setTypedef(false);
			return origin;
		} else {
			if(standardTypes.contains(ctx.getText())) {
				return NamedType(ctx.getText());
			} else {
				return DeclaredName(ctx.getText());
			}
		}
	}

	@Override
	public CSimpleType visitTypeSpecifierTypeof(CParser.TypeSpecifierTypeofContext ctx) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public CSimpleType visitTypeQualifier(CParser.TypeQualifierContext ctx) {
		switch(ctx.getText()) {
			case "const": return null;
			case "restrict": throw new UnsupportedOperationException("Not yet implemented!");
			case "volatile": return Volatile();
			case "_Atomic": return Atomic();
		}
		throw new UnsupportedOperationException("Type qualifier " + ctx.getText() + " not expected!");
	}

	@Override
	public CSimpleType visitFunctionSpecifier(CParser.FunctionSpecifierContext ctx) {
		return null;
	}

	@Override
	public CSimpleType visitAlignmentSpecifier(CParser.AlignmentSpecifierContext ctx) {
		return null;
	}

}
