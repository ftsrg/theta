package hu.bme.mit.inf.ttmc.program.cfa.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.program.cfa.CFA;
import hu.bme.mit.inf.ttmc.program.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.program.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.program.stmt.Stmt;

public class CFAEdgeImpl implements CFAEdge {

	final CFA cfa;
	final CFALoc source;
	final CFALoc target;
	final List<Stmt> stmts;
	
	CFAEdgeImpl(final CFA cfa, final CFALoc source, final CFALoc target, List<Stmt> stmts) {
		this.cfa = checkNotNull(cfa);
		this.source = checkNotNull(source);
		this.target = checkNotNull(target);
		this.stmts = ImmutableList.copyOf(checkNotNull(stmts));
	}
	
	@Override
	public CFA getCFA() {
		return cfa;
	}
	
	@Override
	public CFALoc getSource() {
		return source;
	}

	@Override
	public CFALoc getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}
}
