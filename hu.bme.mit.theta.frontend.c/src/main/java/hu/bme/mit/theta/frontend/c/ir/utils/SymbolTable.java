package hu.bme.mit.theta.frontend.c.ir.utils;

import java.util.Map;

import com.google.common.collect.Multimap;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;

public class SymbolTable {

	private Map<String, VarDecl<?>> decls;
	private Multimap<VarDecl<?>, IrNode> defs;
	
}
