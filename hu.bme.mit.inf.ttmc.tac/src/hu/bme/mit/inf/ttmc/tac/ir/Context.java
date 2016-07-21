package hu.bme.mit.inf.ttmc.tac.ir;

import java.util.ArrayList;
import java.util.List;

public class Context {

	private List<TACNode> nodes = new ArrayList<>();

	public void append(TACNode node) {
		this.nodes.add(node);
	}

}
