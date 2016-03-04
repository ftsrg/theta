package hu.bme.mit.inf.ttmc.program.tcfa.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.program.stmt.Stmt;
import hu.bme.mit.inf.ttmc.program.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.program.tcfa.TCFAEdge;

public class MutableTCFAEdgeImpl implements TCFAEdge {

	private MutableTCFAImpl tcfa;
	private MutableTCFALocImpl source;
	private MutableTCFALocImpl target;
	private final List<Stmt> stmts;
	
	MutableTCFAEdgeImpl(final MutableTCFAImpl tcfa, final MutableTCFALocImpl source, final MutableTCFALocImpl target) {
		this.tcfa = tcfa;
		this.source = source;
		this.target = target;
		stmts = new ArrayList<>();
	}

	////

	@Override
	public TCFA getTCFA() {
		return tcfa;
	}
	
	void setTCFA(final MutableTCFAImpl tcfa) {
		this.tcfa = tcfa;
	}

	////

	@Override
	public MutableTCFALocImpl getSource() {
		return source;
	}

	public void setSource(MutableTCFALocImpl source) {
		checkNotNull(source);
		checkArgument(source.getTCFA() == tcfa);
		this.source.removeOutEdge(this);
		source.addOutEdge(this);
		this.source = source;
	}

	////

	@Override
	public MutableTCFALocImpl getTarget() {
		return target;
	}

	public void setTarget(final MutableTCFALocImpl target) {
		checkNotNull(target);
		checkArgument(target.getTCFA() == tcfa);
		this.target.removeInEdge(this);
		target.addOutEdge(this);
		this.target = target;
	}

	////

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}

	////

}
