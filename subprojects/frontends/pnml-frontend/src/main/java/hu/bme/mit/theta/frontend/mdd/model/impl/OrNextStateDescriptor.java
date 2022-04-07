package hu.bme.mit.theta.frontend.mdd.model.impl;

import com.koloboke.collect.map.IntObjMap;
import com.koloboke.collect.map.hash.HashIntObjMaps;
import com.koloboke.collect.map.hash.HashObjObjMaps;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.UniqueTable;
import hu.bme.mit.delta.collections.impl.MapUniqueTable;
import hu.bme.mit.theta.frontend.mdd.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.frontend.mdd.model.StateSpaceInfo;

import java.util.*;
import java.util.stream.Collectors;

public class OrNextStateDescriptor implements AbstractNextStateDescriptor {
	private static final UniqueTable<OrNextStateDescriptor> uniqueTable = new MapUniqueTable<>();
	
	public static void clearUniqueTable() {
		uniqueTable.clear();
	}
	
	private List<AbstractNextStateDescriptor> operands;
	
	private Map<Object, IntObjMapView<AbstractNextStateDescriptor>> diagonalCache = HashObjObjMaps.newUpdatableMap();
	//private IntObjMap<IntObjMapView<AbstractNextStateDescriptor>> offDiagonalCache = HashIntObjMaps.newUpdatableMap();
	
	public static OrNextStateDescriptor create(final List<AbstractNextStateDescriptor> operands) {
		final ArrayList<AbstractNextStateDescriptor> ops = new ArrayList<>(operands);
		ops.sort(Comparator.comparingInt(Object::hashCode));
		
		return uniqueTable.checkIn(new OrNextStateDescriptor(ops));
	}
	
	private OrNextStateDescriptor(final List<AbstractNextStateDescriptor> operands) {
		this.operands = operands;
	}
	
	@Override
	public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(final StateSpaceInfo localStateSpace) {
		class Diagonal implements IntObjMapView<AbstractNextStateDescriptor> {
			private final StateSpaceInfo localStateSpace;
			List<IntObjMapView<AbstractNextStateDescriptor>> diagonals = new ArrayList<>();
			
			private IntObjMap<AbstractNextStateDescriptor> cache = HashIntObjMaps.newUpdatableMap();
			private AbstractNextStateDescriptor defaultValue = null;
			
			Diagonal(List<AbstractNextStateDescriptor> operands, StateSpaceInfo localStateSpace) {
				this.localStateSpace = localStateSpace;
				for (AbstractNextStateDescriptor ns : operands) {
					diagonals.add(ns.getDiagonal(localStateSpace));
				}
			}
			
			@Override
			public boolean isEmpty() {
				for (IntObjMapView<AbstractNextStateDescriptor> diagonal : diagonals) {
					if (!diagonal.isEmpty()) {
						return false;
					}
				}
				return true;
			}
			
			@Override
			public boolean isProcedural() {
				return true;
			}
			
			@Override
			public boolean containsKey(final int key) {
				for (IntObjMapView<AbstractNextStateDescriptor> diagonal : diagonals) {
					if (diagonal.containsKey(key)) {
						return true;
					}
				}
				return false;
			}
			
			@Override
			public AbstractNextStateDescriptor get(final int key) {
				AbstractNextStateDescriptor ret = cache.get(key);
				if (ret != null) {
					return ret;
				}
				List<AbstractNextStateDescriptor> results = new ArrayList<>();
				for (IntObjMapView<AbstractNextStateDescriptor> diagonal : diagonals) {
					final AbstractNextStateDescriptor value = diagonal.get(key);
					if (!AbstractNextStateDescriptor.isNullOrEmpty(value)) {
						results.add(value);
					}
				}
				if (results.isEmpty()) {
					ret = AbstractNextStateDescriptor.terminalEmpty();
				} else 	if (results.size() == 1) {
					ret = results.get(0);
				} else {
					ret = OrNextStateDescriptor.create(results);
				}
				
				cache.put(key, ret);
				return ret;
			}
			
			@Override
			public AbstractNextStateDescriptor defaultValue() {
				if (defaultValue != null) {
					return defaultValue;
				}
				List<AbstractNextStateDescriptor> results = new ArrayList<>();
				for (IntObjMapView<AbstractNextStateDescriptor> diagonal : diagonals) {
					final AbstractNextStateDescriptor value = diagonal.defaultValue();
					if (!AbstractNextStateDescriptor.isNullOrEmpty(value)) {
						results.add(value);
					}
				}
				
				AbstractNextStateDescriptor ret;
				
				if (results.isEmpty()) {
					ret = AbstractNextStateDescriptor.terminalEmpty();
				} else 	if (results.size() == 1) {
					ret = results.get(0);
				} else {
					ret = OrNextStateDescriptor.create(results);
				}
				defaultValue = ret;
				return ret;
			}
			
			@Override
			public IntObjCursor<? extends AbstractNextStateDescriptor> cursor() {
				// TODO: Auto-generated method stub.
				throw new UnsupportedOperationException("Not (yet) implemented.");
				//return 0;
			}
			
			@Override
			public int size() {
				// TODO: Auto-generated method stub.
				throw new UnsupportedOperationException("Not (yet) implemented.");
				//return 0;
			}
		};
		
		IntObjMapView<AbstractNextStateDescriptor> ret = diagonalCache.computeIfAbsent(localStateSpace.getTraceInfo(),
			(o) -> new Diagonal(operands,
			localStateSpace));
		
		return ret;
	}
	
	@Override
	public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(final StateSpaceInfo localStateSpace) {
		// TODO: Auto-generated method stub.
		throw new UnsupportedOperationException("Not (yet) implemented.");
		//return null;
	}
	
	@Override
	public Optional<Iterable<AbstractNextStateDescriptor>> split() {
		return Optional.of(operands);
	}
	
	@Override
	public boolean equals(final Object o) {
		if (this == o) return true;
		if (!(o instanceof OrNextStateDescriptor)) return false;
		
		final OrNextStateDescriptor that = (OrNextStateDescriptor) o;
		
		return operands.equals(that.operands);
	}
	
	private int hashCode = 0;
	
	@Override
	public int hashCode() {
		if (hashCode != 0) {
			return hashCode;
		}
		return hashCode = operands.hashCode();
	}
	
	@Override
	public String toString() {
		return operands.stream().map(ns -> ns.toString()).collect(Collectors.joining(", "));
	}
}
