package hu.bme.mit.inf.ttmc.code.ast;

import java.util.EnumSet;

public class DeclarationSpecifierAst extends AstNode {

	public enum StorageClassSpecifier {
		TYPEDEF, EXTERN, STATIC, AUTO, REGISTER		
	}
	
	public enum TypeQualifier {
		CONST, RESTRICT, VOLATILE
	}
	
	public enum TypeEnum {
		VOID, CHAR, SHORT, INT, LONG, FLOAT, DOUBLE, SIGNED, UNSIGNED
	}
	
	public enum FunctionSpecifier {
		INLINE
	}
		
	private EnumSet<StorageClassSpecifier> storageSpec;
	private EnumSet<TypeQualifier> typeQualifier;
	private EnumSet<FunctionSpecifier> functionSpec;
	
	public DeclarationSpecifierAst() {
		this.storageSpec = EnumSet.noneOf(StorageClassSpecifier.class);
		this.typeQualifier = EnumSet.noneOf(TypeQualifier.class);
		this.functionSpec = EnumSet.noneOf(FunctionSpecifier.class);
	}
	
	public DeclarationSpecifierAst(
		EnumSet<StorageClassSpecifier> storageSpec,
		EnumSet<TypeQualifier> typeQualifier,
		EnumSet<FunctionSpecifier> functionSpec
	) {
		this.storageSpec = storageSpec;
		this.typeQualifier = typeQualifier;
		this.functionSpec = functionSpec;
	}
	
	public final EnumSet<StorageClassSpecifier> getStorageClassSpecifier() {
		return this.storageSpec;
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
