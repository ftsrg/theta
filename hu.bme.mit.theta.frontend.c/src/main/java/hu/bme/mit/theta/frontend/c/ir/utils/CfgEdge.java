package hu.bme.mit.theta.frontend.c.ir.utils;

import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.common.Product2;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;

public class CfgEdge {

	private final BasicBlock from;
	private final BasicBlock to;
	
	private final Optional<Expr<? extends BoolType>> guard;
	
	public CfgEdge(BasicBlock from, BasicBlock to) {
		this.from = from;
		this.to = to;
		this.guard = Optional.empty();
	}

	public CfgEdge(BasicBlock from, BasicBlock to, Expr<? extends BoolType> guard) {
		this.from = from;
		this.to = to;
		this.guard = Optional.of(guard);
	}

	public BasicBlock getFrom() {
		return from;
	}

	public BasicBlock getTo() {
		return to;
	}

	public boolean hasGuard() {
		return this.guard.isPresent();
	}
	
	public Expr<? extends BoolType> getGuard() {
		return this.guard.get();
	}
	
	@Override
	public boolean equals(Object obj) {
		if (obj == null)
			return false;
		
		if (obj == this)
			return true;
    
		if (!(obj instanceof CfgEdge))
			return false;

		CfgEdge cfgEdge = (CfgEdge) obj;
		
		return cfgEdge.from.equals(this.from) && cfgEdge.to.equals(this.to);
	}
	
	@Override
	public String toString() {
		return "(" + this.from.toString() + ", " + this.to.toString() + ")";
	}
	
	
}
