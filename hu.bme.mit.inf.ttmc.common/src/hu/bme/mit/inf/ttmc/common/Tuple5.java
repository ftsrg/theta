package hu.bme.mit.inf.ttmc.common;

public interface Tuple5<T1, T2, T3, T4, T5> extends Tuple {
	
	public T1 _1();
	public T2 _2();
	public T3 _3();
	public T4 _4();
	public T5 _5();
	
	public <T> Tuple5<T, T2, T3, T4, T5> with1(T e);
	public <T> Tuple5<T1, T, T3, T4, T5> with2(T e);
	public <T> Tuple5<T1, T2, T, T4, T5> with3(T e);
	public <T> Tuple5<T1, T2, T3, T, T5> with4(T e);
	public <T> Tuple5<T1, T2, T3, T4, T> with5(T e);
}
