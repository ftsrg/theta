package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

final class CompositeNode extends Node {

	private final Collection<Node> children;

	CompositeNode(final String id, final NodeAttributes attributes) {
		super(id, attributes);
		this.children = new ArrayList<Node>();
	}

	void addChild(final Node child) {
		checkNotNull(child);
		checkArgument(child != this);
		checkArgument(child.getParent() == null);

		children.add(child);
		child.setParent(this);
	}

	public Collection<Node> getChildren() {
		return Collections.unmodifiableCollection(children);
	}
}
