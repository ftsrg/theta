package hu.bme.mit.inf.ttmc.tac.ir;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public class JumpIf implements TACNode {

	private Expr<? extends BoolType> cond;
	private int addr;

	public JumpIf(Expr<? extends BoolType> cond, int addr) {
		this.cond = cond;
		this.addr = addr;
	}

	public Expr<? extends BoolType> getCondition() {
		return this.cond;
	}

	public int getAddress() {
		return this.addr;
	}

	@Override
	public String getLabel() {
		return String.format("JumpIf(%d, %s)", this.addr, this.cond.toString());
	}

}
