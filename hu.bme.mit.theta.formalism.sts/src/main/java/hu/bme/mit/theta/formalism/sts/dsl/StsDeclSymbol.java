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
package hu.bme.mit.theta.formalism.sts.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.common.dsl.ScopedSymbol;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.dsl.ParamBinding;
import hu.bme.mit.theta.core.model.NestedSubstitution;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.StsDeclContext;

final class StsDeclSymbol implements ScopedSymbol {

	private final StsDeclContext stsDeclContext;

	private final StsSpecSymbol enclosingScope;
	private final SymbolTable symbolTable;

	private final String name;
	private final List<ParamDecl<?>> params;

	private StsDeclSymbol(final StsSpecSymbol enclosingScope, final StsDeclContext stsDeclContext) {
		this.enclosingScope = checkNotNull(enclosingScope);
		this.stsDeclContext = checkNotNull(stsDeclContext);
		symbolTable = new SymbolTable();
		name = stsDeclContext.name.getText();
		params = StsDslHelper.createParamList(stsDeclContext.paramDecls);

		declareParams();
	}

	public static StsDeclSymbol create(final StsSpecSymbol enclosingScope, final StsDeclContext tcfaDeclCtx) {
		return new StsDeclSymbol(enclosingScope, tcfaDeclCtx);
	}

	////

	@Override
	public String getName() {
		return name;
	}

	@Override
	public Optional<StsSpecSymbol> enclosingScope() {
		return Optional.of(enclosingScope);
	}

	@Override
	public Optional<Symbol> resolve(final String name) {
		final Optional<Symbol> optSymbol = symbolTable.get(name);
		if (optSymbol.isPresent()) {
			return optSymbol;
		} else {
			return enclosingScope.resolve(name);
		}
	}

	////

	public StsDefScope instantiate(final Substitution assignment, final List<? extends Expr<?>> args) {
		final List<Expr<?>> simplifiedArgs = ExprUtils.simplifyAll(args);
		final ParamBinding binding = ParamBinding.create(params, simplifiedArgs);
		final Substitution newAssignment = NestedSubstitution.create(assignment, binding);
		final StsDefScope stsDefScope = StsCreator.createSts(this, newAssignment, stsDeclContext.def);
		return stsDefScope;
	}

	////

	// TODO Eliminate copy-paste code

	private void declareParams() {
		params.forEach(this::declareParam);
	}

	private void declareParam(final ParamDecl<?> paramDecl) {
		final Symbol symbol = DeclSymbol.of(paramDecl);
		symbolTable.add(symbol);
	}
}
