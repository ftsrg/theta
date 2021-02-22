package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.*;

import java.util.*;
import java.util.regex.Pattern;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class XstsSpecification implements Scope {

	private final SymbolTable symbolTable;
	private final SymbolTable typeTable;
	private final XstsContext context;

	private final Pattern tempVarPattern = Pattern.compile("temp([0-9])+");

	public XstsSpecification(XstsContext context){
		this.context = checkNotNull(context);
		this.symbolTable = new SymbolTable();
		this.typeTable = new SymbolTable();
	}

	@Override
	public Optional<? extends Scope> enclosingScope() {
		return Optional.empty();
	}

	@Override
	public Optional<? extends Symbol> resolve(String name) {
		return symbolTable.get(name);
	}

	private void checkIfTempVar(String name) {
		if (tempVarPattern.matcher(name).matches()) throw new RuntimeException(name + " is reserved!");
	}

	public XSTS instantiate(){
		final Env env = new Env();

		final Map<VarDecl<?>, XstsTypeDeclSymbol> varToType = new HashMap<>();
		final Set<VarDecl<?>> ctrlVars = new HashSet<>();
		final List<Expr<BoolType>> initExprs = new ArrayList<>();

		for(var typeDeclContext: context.typeDeclarations){
			final List<XstsTypeLiteralSymbol> literals = new ArrayList<>();
			for(var literalContext: typeDeclContext.literals){
				var optSymbol = symbolTable.get(literalContext.name.getText());
				if(optSymbol.isPresent()){
					literals.add((XstsTypeLiteralSymbol) optSymbol.get());
				} else {
					var symbol = new XstsTypeLiteralSymbol(literalContext.name.getText());
					literals.add(symbol);
					symbolTable.add(symbol);
					env.define(symbol,symbol.instantiate());
				}
			}

			final XstsTypeDeclSymbol typeDeclSymbol = XstsTypeDeclSymbol.of(typeDeclContext.name.getText(),literals);
			typeTable.add(typeDeclSymbol);
			env.define(typeDeclSymbol,typeDeclSymbol.instantiate());
		}

		for(var varDeclContext: context.variableDeclarations){
			final XstsVariableSymbol symbol = new XstsVariableSymbol(typeTable,varDeclContext);
			symbolTable.add(symbol);

			final VarDecl<?> var = symbol.instantiate(env);
			final Optional<? extends Symbol> typeDeclSymbol = typeTable.get(varDeclContext.ttype.getText());
			if (!typeDeclSymbol.isEmpty()) {
				varToType.put(var, (XstsTypeDeclSymbol) typeDeclSymbol.get());
			}
			if(varDeclContext.CTRL()!=null) ctrlVars.add(var);
			if(varDeclContext.initValue!=null){
				initExprs.add(Eq(var.getRef(),new XstsExpression(this,typeTable,varDeclContext.initValue).instantiate(env)));
			}
			env.define(symbol,var);
		}

		final Expr<BoolType> initFormula = And(initExprs);

		final NonDetStmt tranSet = new XstsTransitionSet(this,typeTable,context.tran.transitionSet()).instantiate(env);
		final NonDetStmt initSet = new XstsTransitionSet(this,typeTable,context.init.transitionSet()).instantiate(env);
		final NonDetStmt envSet = new XstsTransitionSet(this,typeTable,context.env.transitionSet()).instantiate(env);

		final Expr<BoolType> prop = cast(new XstsExpression(this,typeTable,context.prop).instantiate(env),Bool());

		return new XSTS(varToType,ctrlVars,initSet,tranSet,envSet,initFormula,prop);
	}
}
