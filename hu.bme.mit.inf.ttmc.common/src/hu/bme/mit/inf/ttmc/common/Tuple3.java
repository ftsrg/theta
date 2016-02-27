package hu.bme.mit.inf.ttmc.common;

public interface Tuple3<T1, T2, T3> extends Tuple {

	public T1 _1();
	public T2 _2();
	public T3 _3();
	
	public <T> Tuple3<T, T2, T3> with1(T e);
	public <T> Tuple3<T1, T, T3> with2(T e);
	public <T> Tuple3<T1, T2, T> with3(T e);
}
