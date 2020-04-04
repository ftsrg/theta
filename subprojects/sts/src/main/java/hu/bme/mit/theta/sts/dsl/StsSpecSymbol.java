/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.sts.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.sts.dsl.StsDslHelper.createConstDecl;
import static hu.bme.mit.theta.sts.dsl.StsDslHelper.createVarDecl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.ScopedSymbol;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.dsl.ParamBinding;
import hu.bme.mit.theta.core.model.NestedSubstitution;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.ConstDeclContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.PropDeclContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.StsDeclContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.StsSpecContext;
import hu.bme.mit.theta.sts.dsl.gen.StsDslParser.VarDeclContext;

final class StsSpecSymbol implements ScopedSymbol {

	private final StsSpecContext stsSpecContext;

	private final SymbolTable symbolTable;

	private final String name;
	private final List<ParamDecl<?>> params;

	private final Collection<PropDeclSymbol> propDeclSymbols;

	private StsSpecSymbol(final StsSpecContext StsSpecContext) {
		this.stsSpecContext = checkNotNull(StsSpecContext);
		symbolTable = new SymbolTable();
		name = StsSpecContext.name.getText();
		params = StsDslHelper.createParamList(StsSpecContext.paramDecls);

		propDeclSymbols = new ArrayList<>();

		declareParams();
		declareConsts();
		declareVars();
		declareStss();
		declareProps();
	}

	public static StsSpecSymbol create(final StsSpecContext stsSpecContext) {
		return new StsSpecSymbol(stsSpecContext);
	}

	////

	public Collection<PropDeclSymbol> getPropDeclSymbols() {
		return Collections.unmodifiableCollection(propDeclSymbols);
	}

	////

	@Override
	public String getName() {
		return name;
	}

	@Override
	public Optional<Scope> enclosingScope() {
		return Optional.empty();
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		return symbolTable.get(name);
	}

	////

	public StsSpec instantiate(final List<? extends Expr<?>> args) {
		final List<Expr<?>> simplifiedArgs = ExprUtils.simplifyAll(args);
		final ParamBinding binding = ParamBinding.create(params, simplifiedArgs);
		// TODO Handle recursive constant definitions
		final Substitution constAssignment = StsDslHelper.createConstDefs(this, binding, stsSpecContext.constDecls);
		final Substitution assignment = NestedSubstitution.create(binding, constAssignment);
		final StsSpec stsSpec = StsSpec.create(this, assignment);
		return stsSpec;
	}

	////

	private void declareParams() {
		params.forEach(this::declareParam);
	}

	private void declareParam(final ParamDecl<?> paramDecl) {
		final Symbol symbol = DeclSymbol.of(paramDecl);
		symbolTable.add(symbol);
	}

	private void declareConsts() {
		stsSpecContext.constDecls.forEach(this::declareConst);
	}

	private void declareConst(final ConstDeclContext constDeclContext) {
		final ConstDecl<?> constDecl = createConstDecl(constDeclContext);
		final Symbol symbol = DeclSymbol.of(constDecl);
		symbolTable.add(symbol);
	}

	private void declareVars() {
		stsSpecContext.varDecls.forEach(this::declareVar);
	}

	private void declareVar(final VarDeclContext varDeclContext) {
		final VarDecl<?> varDecl = createVarDecl(varDeclContext);
		final Symbol symbol = DeclSymbol.of(varDecl);
		symbolTable.add(symbol);
	}

	private void declareStss() {
		stsSpecContext.stsDecls.forEach(this::declareSts);
	}

	private void declareSts(final StsDeclContext stsDeclContext) {
		final StsDeclSymbol symbol = StsDeclSymbol.create(this, stsDeclContext);
		symbolTable.add(symbol);
	}

	private void declareProps() {
		stsSpecContext.propDecls.forEach(this::declareProp);
	}

	private void declareProp(final PropDeclContext propDeclContext) {
		final PropDeclSymbol symbol = PropDeclSymbol.create(this, propDeclContext);
		propDeclSymbols.add(symbol);
		symbolTable.add(symbol);
	}

}
