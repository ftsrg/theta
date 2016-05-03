package hu.bme.mit.inf.ttmc.code.ast.factory;

import java.util.EnumSet;
import java.util.List;

import hu.bme.mit.inf.ttmc.code.ast.DeclarationSpecifierAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.InitializerAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationSpecifierAst.FunctionSpecifier;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationSpecifierAst.StorageClassSpecifier;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationSpecifierAst.TypeQualifier;

public class DeclarationAstFactory {

	public static VarDeclarationAst varDecl(DeclarationSpecifierAst specifier, List<DeclaratorAst> declarators) {
		return new VarDeclarationAst(specifier, declarators);
	}
	
	public static VarDeclarationAst varDecl(DeclarationSpecifierAst specifier, DeclaratorAst declarator) {
		return new VarDeclarationAst(specifier, declarator);
	}
	
	public static VarDeclarationAst varDecl(
		EnumSet<StorageClassSpecifier> storageSpec,
		EnumSet<TypeQualifier> typeQualifier,
		DeclaratorAst declarator
	) {
		return new VarDeclarationAst(
			new DeclarationSpecifierAst(
				storageSpec,
				typeQualifier,
				EnumSet.noneOf(DeclarationSpecifierAst.FunctionSpecifier.class)
			),
			declarator
		);
	}
	
	public static VarDeclarationAst varDecl(DeclaratorAst declarator) {
		return varDecl(
			EnumSet.noneOf(DeclarationSpecifierAst.StorageClassSpecifier.class),
			EnumSet.noneOf(DeclarationSpecifierAst.TypeQualifier.class),
			declarator
		);
	}
	
	public static InitDeclaratorAst initDecl(String name) {
		return new InitDeclaratorAst(name);
	}
	
	public static DeclaratorAst initDecl(String name, InitializerAst init) {
		return new InitDeclaratorAst(name, init);
	}
		
	
}
