package hu.bme.mit.theta.common.visualization;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.awt.Color;
import java.util.ArrayList;
import java.util.Collection;

public final class CompositeNode extends Node {

	private final Collection<Node> children;

	public CompositeNode(final String id, final String label, final Color fillColor, final Color edgeColor,
			final String lineStyle) {
		super(id, label, fillColor, edgeColor, lineStyle);
		this.children = new ArrayList<Node>();
	}

	public void addChild(final Node child) {
		checkNotNull(child);
		checkArgument(child != this);

		children.add(child);
	}
}
