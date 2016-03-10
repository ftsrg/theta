package hu.bme.mit.inf.ttmc.common;

public interface Tuple7<T1, T2, T3, T4, T5, T6, T7> extends Tuple {
	
	public T1 _1();
	public T2 _2();
	public T3 _3();
	public T4 _4();
	public T5 _5();
	public T6 _6();
	public T7 _7();
	
	public <T> Tuple7<T, T2, T3, T4, T5, T6, T7> with1(T e);
	public <T> Tuple7<T1, T, T3, T4, T5, T6, T7> with2(T e);
	public <T> Tuple7<T1, T2, T, T4, T5, T6, T7> with3(T e);
	public <T> Tuple7<T1, T2, T3, T, T5, T6, T7> with4(T e);
	public <T> Tuple7<T1, T2, T3, T4, T, T6, T7> with5(T e);
	public <T> Tuple7<T1, T2, T3, T4, T5, T, T7> with6(T e);
	public <T> Tuple7<T1, T2, T3, T4, T5, T6, T> with7(T e);
	
	
}
