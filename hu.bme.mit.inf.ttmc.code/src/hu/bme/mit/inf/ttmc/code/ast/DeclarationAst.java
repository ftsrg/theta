package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.DeclarationVisitor;

abstract public class DeclarationAst extends AstNode {

	abstract public<D> D accept(DeclarationVisitor<D> visitor);
}
