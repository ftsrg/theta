package hu.bme.mit.theta.core.utils;

public interface Lens<T, E> {

    E get(T t);

    T set(T t, E e);

}
