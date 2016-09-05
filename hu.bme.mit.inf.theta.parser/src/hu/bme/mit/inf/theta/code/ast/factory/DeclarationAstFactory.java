package hu.bme.mit.inf.theta.code.ast.factory;

import java.util.EnumSet;
import java.util.List;

import hu.bme.mit.inf.theta.code.ast.DeclarationSpecifierAst;
import hu.bme.mit.inf.theta.code.ast.DeclarationSpecifierAst.StorageClassSpecifier;
import hu.bme.mit.inf.theta.code.ast.DeclarationSpecifierAst.TypeQualifier;
import hu.bme.mit.inf.theta.code.ast.DeclaratorAst;
import hu.bme.mit.inf.theta.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.theta.code.ast.InitializerAst;
import hu.bme.mit.inf.theta.code.ast.VarDeclarationAst;

public class DeclarationAstFactory {

	public static VarDeclarationAst VarDecl(DeclarationSpecifierAst specifier, List<DeclaratorAst> declarators) {
		return new VarDeclarationAst(specifier, declarators);
	}
	
	public static VarDeclarationAst VarDecl(DeclarationSpecifierAst specifier, DeclaratorAst declarator) {
		return new VarDeclarationAst(specifier, declarator);
	}
	
	public static VarDeclarationAst VarDecl(
		StorageClassSpecifier storageSpec,
		EnumSet<TypeQualifier> typeQualifiers,
		DeclaratorAst declarator
	) {
		return new VarDeclarationAst(
			new DeclarationSpecifierAst(
				storageSpec,
				typeQualifiers
			),
			declarator
		);
	}
	
	public static VarDeclarationAst VarDecl(DeclaratorAst declarator) {
		return VarDecl(
			DeclarationSpecifierAst.StorageClassSpecifier.NONE,
			EnumSet.noneOf(DeclarationSpecifierAst.TypeQualifier.class),
			declarator
		);
	}
	
	public static InitDeclaratorAst InitDeclarator(String name) {
		return new InitDeclaratorAst(name);
	}
	
	public static DeclaratorAst InitDeclarator(String name, InitializerAst init) {
		return new InitDeclaratorAst(name, init);
	}
		
	
}
