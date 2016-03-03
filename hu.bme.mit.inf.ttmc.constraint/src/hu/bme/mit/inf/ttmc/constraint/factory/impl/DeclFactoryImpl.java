package hu.bme.mit.inf.ttmc.constraint.factory.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.impl.ConstDeclImpl;
import hu.bme.mit.inf.ttmc.constraint.decl.impl.ParamDeclImpl;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class DeclFactoryImpl implements DeclFactory {

	private final HashMap<String, ConstDecl<?>> nameToConst;
	
	public DeclFactoryImpl() {
		nameToConst = new HashMap<String, ConstDecl<?>>();
	}

	@Override
	public <T extends Type> ConstDecl<T> Const(String name, T type) {
		checkNotNull(name);
		checkNotNull(type);
		checkArgument(name.length() > 0);
		checkArgument(nameToConst.get(name) == null);
		
		final ConstDecl<T> constDecl = new ConstDeclImpl<>(name, type);
		nameToConst.put(name, constDecl);
		return constDecl;
	}

	@Override
	public <T extends Type> ParamDecl<T> Param(String name, T type) {
		checkNotNull(name);
		checkNotNull(type);
		checkArgument(name.length() > 0);
		final ParamDecl<T> paramDecl = new ParamDeclImpl<T>(name, type);
		return paramDecl;
	}

}
