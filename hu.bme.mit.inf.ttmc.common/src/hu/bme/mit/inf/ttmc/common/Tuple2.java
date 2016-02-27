package hu.bme.mit.inf.ttmc.common;

public interface Tuple2<T1, T2> extends Tuple {
	
	public T1 _1();
	public T2 _2();
	
	public <T> Tuple2<T, T2> with1(T e);
	public <T> Tuple2<T1, T> with2(T e);
	
}
