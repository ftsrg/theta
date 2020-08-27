package hu.bme.mit.theta.solver.smtlib;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Maps;
import hu.bme.mit.theta.core.decl.ConstDecl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public class SmtLibSymbolTable {
    private final BiMap<ConstDecl<?>, String> constToSymbol;
    private final BiMap<ConstDecl<?>, String> constToDeclaration;

    public SmtLibSymbolTable() {
        constToSymbol = Maps.synchronizedBiMap(HashBiMap.create());
        constToDeclaration = Maps.synchronizedBiMap(HashBiMap.create());
    }

    public boolean definesConst(final ConstDecl<?> constDecl) {
        return constToSymbol.containsKey(constDecl);
    }

    public boolean definesSymbol(final String symbol) {
        return constToSymbol.inverse().containsKey(symbol);
    }

    public String getSymbol(final ConstDecl<?> constDecl) {
        checkArgument(definesConst(constDecl));
        return constToSymbol.get(constDecl);
    }

    public String getDeclaration(final ConstDecl<?> constDecl) {
        checkArgument(definesConst(constDecl));
        return constToDeclaration.get(constDecl);
    }

    public ConstDecl<?> getConst(final String symbol) {
        checkArgument(definesSymbol(symbol));
        return constToSymbol.inverse().get(symbol);
    }

    public void put(final ConstDecl<?> constDecl, final String symbol, final String declaration) {
        checkNotNull(constDecl);
        checkNotNull(symbol);
        checkNotNull(declaration);
        checkState(!constToSymbol.containsKey(constDecl), "Constant not found.");
        constToSymbol.put(constDecl, symbol);
        constToDeclaration.put(constDecl, declaration);
    }
}
