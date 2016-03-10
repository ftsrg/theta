package hu.bme.mit.inf.ttmc.common;

public interface Tuple4<T1, T2, T3, T4> extends Tuple {
	
	public T1 _1();
	public T2 _2();
	public T3 _3();
	public T4 _4();
	
	public <T> Tuple4<T, T2, T3, T4> with1(T e);
	public <T> Tuple4<T1, T, T3, T4> with2(T e);
	public <T> Tuple4<T1, T2, T, T4> with3(T e);
	public <T> Tuple4<T1, T2, T3, T> with4(T e);
	
}
