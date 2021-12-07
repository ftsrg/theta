package hu.bme.mit.theta.analysis;

public interface Lens<T, E> {

    E get(T t);

    T set(T t, E e);

}
