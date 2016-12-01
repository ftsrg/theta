package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.DeclarationVisitor;

abstract public class DeclarationAst extends AstNode {

	abstract public <D> D accept(DeclarationVisitor<D> visitor);

	@Override
	abstract public DeclarationAst copy();
}
