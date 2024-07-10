package hu.bme.mit.theta.frontend.mdd.ptnet;

import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.theta.frontend.petrinet.model.Place;
import hu.bme.mit.theta.frontend.petrinet.model.Transition;
import hu.bme.mit.theta.frontend.mdd.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.frontend.mdd.model.StateSpaceInfo;

import java.util.NoSuchElementException;

import static hu.bme.mit.theta.frontend.mdd.model.AbstractNextStateDescriptor.*;

public final class PtNetTransitionNextStateDescriptor implements AbstractNextStateDescriptor {
	private Transition representedTransition;
	private Place affectedPlace;
	private int takes;
	private int inhibits = Integer.MAX_VALUE;
	private int puts;
	private AbstractNextStateDescriptor continuation;
	private int hashCode = 0;
	
	public PtNetTransitionNextStateDescriptor(
		final Transition representedTransition,
		final Place affectedPlace,
		final int takes,
		final int inhibits,
		final int puts,
		final AbstractNextStateDescriptor continuation
	) {
		this.representedTransition = representedTransition;
		this.affectedPlace = affectedPlace;
		this.takes = takes;
		this.inhibits = inhibits;
		this.puts = puts;
		this.continuation = continuation;
	}
	
	@Override
	public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(final StateSpaceInfo localStateSpace) {
		if (localStateSpace.getTraceInfo() == affectedPlace) {
			return new IntObjMapView<AbstractNextStateDescriptor>() {
				@Override
				public boolean isEmpty() {
					// diagonal is empty if edge is not test or never enabled
					return takes != puts || takes >= inhibits;
				}
				
				@Override
				public boolean isProcedural() {
					return true;
				}
				
				@Override
				public boolean containsKey(final int key) {
					return !isEmpty() && key >= takes && key < inhibits;
				}
				
				@Override
				public AbstractNextStateDescriptor get(final int key) {
					if (containsKey(key)) {
						return continuation;
					} else {
						return defaultValue();
					}
				}
				
				@Override
				public AbstractNextStateDescriptor defaultValue() {
					return terminalEmpty();
				}
				
				@Override
				public IntObjCursor<? extends AbstractNextStateDescriptor> cursor() {
					return new IntObjCursor<AbstractNextStateDescriptor>() {
						int current = takes - 1;
						@Override
						public int key() {
							if (!containsKey(current)) {
								throw new NoSuchElementException();
							}
							return current;
						}
						
						@Override
						public AbstractNextStateDescriptor value() {
							if (!containsKey(current)) {
								throw new NoSuchElementException();
							}
							return continuation;
						}
						
						@Override
						public boolean moveNext() {
							return ++current < inhibits;
						}
					};
				}
				
				@Override
				public int size() {
					return (inhibits == Integer.MAX_VALUE) ? -1 : inhibits - takes;
				}
			};
		} else {
			return IntObjMapView.empty(this);
		}
	}
	
	@Override
	public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(final StateSpaceInfo localStateSpace) {
		if (localStateSpace.getTraceInfo() == affectedPlace) {
			return new IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>>() {
				@Override
				public boolean isEmpty() {
					// diagonal is empty if edge is not test or never enabled
					return takes == puts || takes >= inhibits;
				}
				
				@Override
				public boolean isProcedural() {
					return true;
				}
				
				@Override
				public boolean containsKey(final int key) {
					return !isEmpty() && key >= takes && key < inhibits;
				}
				
				@Override
				public IntObjMapView<AbstractNextStateDescriptor> get(final int from) {
					if (containsKey(from)) {
						return new IntObjMapView<AbstractNextStateDescriptor>() {
							@Override
							public boolean isEmpty() {
								return false;
							}
							
							@Override
							public boolean isProcedural() {
								return false;
							}
							
							@Override
							public boolean containsKey(final int to) {
								return to == from - takes + puts;
							}
							
							@Override
							public AbstractNextStateDescriptor get(final int to) {
								if (containsKey(to)) {
									return continuation;
								} else {
									return defaultValue();
								}
							}
							
							@Override
							public AbstractNextStateDescriptor defaultValue() {
								return terminalEmpty();
							}
							
							@Override
							public IntObjCursor<? extends AbstractNextStateDescriptor> cursor() {
								return new IntObjCursor<AbstractNextStateDescriptor>() {
									int current = from - takes + puts - 1;
									@Override
									public int key() {
										if (!containsKey(current)) {
											throw new NoSuchElementException();
										}
										return current;
									}
									
									@Override
									public AbstractNextStateDescriptor value() {
										if (!containsKey(current)) {
											throw new NoSuchElementException();
										}
										return continuation;
									}
									
									@Override
									public boolean moveNext() {
										return ++current <= from - takes + puts;
									}
								};
							}
							
							@Override
							public int size() {
								return 1;
							}
						};
					} else {
						return defaultValue();
					}
				}
				
				@Override
				public IntObjMapView<AbstractNextStateDescriptor> defaultValue() {
					return IntObjMapView.empty();
				}
				
				@Override
				public IntObjCursor<? extends IntObjMapView<AbstractNextStateDescriptor>> cursor() {
					return new IntObjCursor<IntObjMapView<AbstractNextStateDescriptor>>() {
						int current = takes - 1;
						@Override
						public int key() {
							if (!containsKey(current)) {
								throw new NoSuchElementException();
							}
							return current;
						}
						
						@Override
						public IntObjMapView<AbstractNextStateDescriptor> value() {
							if (!containsKey(current)) {
								throw new NoSuchElementException();
							}
							return get(current);
						}
						
						@Override
						public boolean moveNext() {
							return ++current < inhibits;
						}
					};
				}
				
				@Override
				public int size() {
					return (inhibits == Integer.MAX_VALUE) ? -1 : inhibits - takes;
				}
			};
		} else {
			return IntObjMapView.empty(IntObjMapView.empty(AbstractNextStateDescriptor.terminalEmpty()));
		}
	}
	
	@Override
	public boolean equals(final Object o) {
		if (this == o) return true;
		if (!(o instanceof PtNetTransitionNextStateDescriptor)) return false;
		
		final PtNetTransitionNextStateDescriptor that = (PtNetTransitionNextStateDescriptor) o;
		
		if (takes != that.takes) return false;
		if (inhibits != that.inhibits) return false;
		if (puts != that.puts) return false;
		if (affectedPlace != null ? !affectedPlace.equals(that.affectedPlace) : that.affectedPlace != null)
			return false;
		return continuation != null ? continuation.equals(that.continuation) : that.continuation == null;
	}
	
	@Override
	public int hashCode() {
		if (hashCode != 0) {
			return hashCode;
		}
		hashCode = affectedPlace != null ? affectedPlace.hashCode() : 0;
		hashCode = 31 * hashCode + takes;
		hashCode = 31 * hashCode + inhibits;
		hashCode = 31 * hashCode + puts;
		hashCode = 31 * hashCode + (continuation != null ? continuation.hashCode() : 0);
		return hashCode;
	}
	
	@Override
	public String toString() {
		return representedTransition.toString();
	}
}
