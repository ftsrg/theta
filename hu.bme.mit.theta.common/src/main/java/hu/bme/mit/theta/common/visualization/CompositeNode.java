package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.awt.Color;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

final class CompositeNode extends Node {

	private final Collection<Node> children;

	CompositeNode(final String id, final String label, final Color fillColor, final Color edgeColor,
			final String lineStyle, final int peripheries) {
		super(id, label, fillColor, edgeColor, lineStyle, peripheries);
		this.children = new ArrayList<Node>();
	}

	void addChild(final Node child) {
		checkNotNull(child);
		checkArgument(child != this);

		children.add(child);
	}

	public Collection<Node> getChildren() {
		return Collections.unmodifiableCollection(children);
	}
}
