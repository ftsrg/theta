package hu.bme.mit.theta.frontend.c.parser.ast;

import java.util.EnumSet;

public class DeclarationSpecifierAst extends AstNode {

	public enum StorageClassSpecifier {
		TYPEDEF, EXTERN, STATIC, AUTO, REGISTER, NONE
	}

	public enum TypeQualifier {
		CONST, RESTRICT, VOLATILE,
	}

	public enum TypeSpecifier {
		VOID, CHAR, SHORT, INT, LONG, FLOAT, DOUBLE, SIGNED, UNSIGNED,
		// TODO: struct/union spec, enum spec, arbitrary type name
	}

	public enum FunctionSpecifier {
		INLINE, NONE
	}

	private StorageClassSpecifier storageSpec;
	private EnumSet<TypeQualifier> typeQualifier;
	private FunctionSpecifier functionSpec;

	public DeclarationSpecifierAst() {
		this.storageSpec = StorageClassSpecifier.NONE;
		this.functionSpec = FunctionSpecifier.NONE;
		this.typeQualifier = EnumSet.noneOf(TypeQualifier.class);
	}

	public DeclarationSpecifierAst(StorageClassSpecifier storageSpec, EnumSet<TypeQualifier> typeQualifiers,
			FunctionSpecifier functionSpec) {
		this.storageSpec = storageSpec;
		this.typeQualifier = typeQualifiers;
		this.functionSpec = functionSpec;
	}

	public DeclarationSpecifierAst(StorageClassSpecifier storageSpec, EnumSet<TypeQualifier> typeQualifiers) {
		this.storageSpec = storageSpec;
		this.typeQualifier = typeQualifiers;
		this.functionSpec = FunctionSpecifier.NONE;
	}

	public final StorageClassSpecifier getStorageClassSpecifier() {
		return this.storageSpec;
	}

	public EnumSet<TypeQualifier> getTypeQualifier() {
		return this.typeQualifier;
	}

	public FunctionSpecifier getFunctionSpecifier() {
		return this.functionSpec;
	}

	@Override
	public AstNode[] getChildren() {
		return new AstNode[] {};
	}

	@Override
	public DeclarationSpecifierAst copy() {
		throw new UnsupportedOperationException();
	}

}
