package hu.bme.mit.theta.xcfa.dsl;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser;

import java.util.Optional;

public class XcfaSymbol implements Scope {

    private SymbolTable symbolTable;

    XcfaSymbol(final XcfaDslParser.SpecContext context) {
        symbolTable = new SymbolTable();
        context.varDecls.forEach(varDeclContext -> symbolTable.add(new XcfaVariableSymbol(varDeclContext)));
        context.processDecls.forEach(processDeclContext -> symbolTable.add(new XcfaProcessSymbol(this, processDeclContext)));
    }

    @Override
    public Optional<? extends Scope> enclosingScope() {
        return Optional.empty();
    }

    @Override
    public Optional<? extends Symbol> resolve(String name) {
        return symbolTable.get(name);
    }

}
