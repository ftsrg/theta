package hu.bme.mit.theta.analysis.algorithm.symbolic.mdd;

import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;

public final class MddStateSpaceInfo implements StateSpaceInfo {
	private final MddVariable variable;
	private final MddNode     mddNode;
	
	public MddStateSpaceInfo(final MddVariable variable, final MddNode mddNode) {
		this.variable = variable;
		this.mddNode = mddNode;
	}
	
	@Override
	public Object getTraceInfo() {
		return variable.getTraceInfo();
	}
	
	// @Override
	// public ElementChain<Object> getComponentChain() {
	// 	class TraceInfoChain implements ElementChain<Object> {
	// 		private final MddVariableHandle mddVariableHandle;
	//
	// 		TraceInfoChain(MddVariableHandle mddVariableHandle) {
	// 			Preconditions.checkArgument(mddVariableHandle.getVariable().isPresent());
	// 			this.mddVariableHandle = mddVariableHandle;
	// 		}
	//
	// 		@Override
	// 		public Object getElement() {
	// 			return mddVariableHandle.getVariable().orElseThrow(AssertionError::new).getTraceInfo();
	// 		}
	//
	// 		@Override
	// 		public ElementChain<Object> next() {
	// 			if (mddVariableHandle.getLower().isPresent()) {
	// 				return new TraceInfoChain(mddVariableHandle.getLower().orElseThrow(AssertionError::new));
	// 			} else {
	// 				return null;
	// 			}
	// 		}
	// 	}
	//
	// 	return new TraceInfoChain(variableHandle);
	// }
	
	// TODO: else nodes are problematic, better not use them for now
	@Override
	public boolean hasInfiniteStates() {
		if (mddNode.isTerminal()) {
			return true;
		} else if (mddNode.isBelow(variable)) {
			return true;
		} else {
			return !variable.isNullOrZero(mddNode.defaultValue());
		}
	}
	
	@Override
	public IntSetView getLocalStateSpace() {
		return mddNode.keySet();
	}
	
	// @Override
	// public StateSpaceInfo getLocalStateSpace(final Object someLowerComponent) {
	// 	// TODO: Auto-generated method stub.
	// 	throw new UnsupportedOperationException("Not (yet) implemented.");
	// 	//return null;
	// }
}
