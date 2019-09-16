package hu.bme.mit.theta.xcfa.dsl;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class XcfaSymbol implements Scope {

    private SymbolTable symbolTable;

    private final List<XcfaVariableSymbol> vars;
    private final List<XcfaProcessSymbol> processes;

    XcfaSymbol(final XcfaDslParser.SpecContext context) {
        symbolTable = new SymbolTable();
        vars = new ArrayList<>();
        processes = new ArrayList<>();
        context.varDecls.forEach(varDeclContext -> {
            XcfaVariableSymbol var;
            symbolTable.add(var = new XcfaVariableSymbol(varDeclContext));
            vars.add(var);
        });
        context.processDecls.forEach(processDeclContext -> {
            XcfaProcessSymbol proc;
            symbolTable.add(proc = new XcfaProcessSymbol(this, processDeclContext));
            processes.add(proc);
        });
    }


    XCFA instantiate() {
        XCFA.Builder builder = XCFA.builder();
        vars.forEach(xcfaVariableSymbol -> builder.createVar(xcfaVariableSymbol.instantiate()));
        processes.forEach(xcfaProcessSymbol -> builder.addProcess(xcfaProcessSymbol.instantiate()));
        return builder.build();
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
