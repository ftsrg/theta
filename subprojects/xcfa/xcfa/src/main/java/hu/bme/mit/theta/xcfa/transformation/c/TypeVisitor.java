package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.xcfa.dsl.gen.CParser;
import hu.bme.mit.theta.xcfa.transformation.c.types.CType;
import hu.bme.mit.theta.xcfa.transformation.c.types.Enum;
import hu.bme.mit.theta.xcfa.transformation.c.types.NamedType;
import hu.bme.mit.theta.xcfa.transformation.c.types.Typedef;
import hu.bme.mit.theta.xcfa.transformation.c.types.Volatile;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.xcfa.transformation.c.types.CTypeFactory.Atomic;
import static hu.bme.mit.theta.xcfa.transformation.c.types.CTypeFactory.Extern;
import static hu.bme.mit.theta.xcfa.transformation.c.types.CTypeFactory.NamedType;
import static hu.bme.mit.theta.xcfa.transformation.c.types.CTypeFactory.Typedef;
import static hu.bme.mit.theta.xcfa.transformation.c.types.CTypeFactory.Volatile;
import static hu.bme.mit.theta.xcfa.transformation.c.types.CTypeFactory.Enum;

public class TypeVisitor extends CBaseVisitor<CType> {

	@Override
	public CType visitDeclarationSpecifiers(CParser.DeclarationSpecifiersContext ctx) {
		List<CType> cTypes = new ArrayList<>();
		for (CParser.DeclarationSpecifierContext declarationSpecifierContext : ctx.declarationSpecifier()) {
			CType ctype = declarationSpecifierContext.accept(this);
			cTypes.add(ctype);
		}

		List<CType> enums = cTypes.stream().filter(cType -> cType instanceof Enum).collect(Collectors.toList());
		checkState(enums.size() <= 1, "Declaration cannot contain more than one enum");
		List<CType> namedElements = cTypes.stream().filter(cType -> cType instanceof NamedType).collect(Collectors.toList());
		CType mainType = enums.size() == 0 ? namedElements.get(0) : enums.get(0);
		cTypes.remove(mainType);
		return mainType.apply(cTypes);
	}

	@Override
	public CType visitStorageClassSpecifier(CParser.StorageClassSpecifierContext ctx) {
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
	public CType visitTypeSpecifierAtomic(CParser.TypeSpecifierAtomicContext ctx) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public CType visitTypeSpecifierCompound(CParser.TypeSpecifierCompoundContext ctx) {
		return ctx.structOrUnionSpecifier().accept(this);
	}

	@Override
	public CType visitCompoundDefinition(CParser.CompoundDefinitionContext ctx) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public CType visitCompoundUsage(CParser.CompoundUsageContext ctx) {
		return NamedType(ctx.structOrUnion().getText() + " " + ctx.Identifier().getText());
	}

	@Override
	public CType visitTypeSpecifierEnum(CParser.TypeSpecifierEnumContext ctx) {
		return ctx.enumSpecifier().accept(this);
	}

	@Override
	public CType visitEnumDefinition(CParser.EnumDefinitionContext ctx) {
		String id = ctx.Identifier() == null ? null : ctx.Identifier().getText();
		Map<String, Optional<Expr<?>>> fields = new LinkedHashMap<>();
		for (CParser.EnumeratorContext enumeratorContext : ctx.enumeratorList().enumerator()) {
			String value = enumeratorContext.enumerationConstant().getText();
			CParser.ConstantExpressionContext expressionContext = enumeratorContext.constantExpression();
			Expr<?> expr = expressionContext == null ? null : expressionContext.accept(null ); // TODO
			fields.put(value, Optional.ofNullable(expr));
		}
		return Enum(id, fields);
	}

	@Override
	public CType visitEnumUsage(CParser.EnumUsageContext ctx) {
		return NamedType("enum " + ctx.Identifier().getText());
	}

	@Override
	public CType visitTypeSpecifierExtension(CParser.TypeSpecifierExtensionContext ctx) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public CType visitTypeSpecifierPointer(CParser.TypeSpecifierPointerContext ctx) {
		CType subtype = ctx.typeSpecifier().accept(this);
		subtype.incrementPointer();
		return subtype;
	}

	@Override
	public CType visitTypeSpecifierSimple(CParser.TypeSpecifierSimpleContext ctx) {
		return NamedType(ctx.getText());
	}

	@Override
	public CType visitTypeSpecifierTypedefName(CParser.TypeSpecifierTypedefNameContext ctx) {
		return NamedType(ctx.getText());
	}

	@Override
	public CType visitTypeSpecifierTypeof(CParser.TypeSpecifierTypeofContext ctx) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public CType visitTypeQualifier(CParser.TypeQualifierContext ctx) {
		switch(ctx.getText()) {
			case "const": return null;
			case "restrict": throw new UnsupportedOperationException("Not yet implemented!");
			case "volatile": return Volatile();
			case "_Atomic": return Atomic();
		}
		throw new UnsupportedOperationException("Type qualifier " + ctx.getText() + " not expected!");
	}

	@Override
	public CType visitFunctionSpecifier(CParser.FunctionSpecifierContext ctx) {
		return null;
	}

	@Override
	public CType visitAlignmentSpecifier(CParser.AlignmentSpecifierContext ctx) {
		return null;
	}

}
