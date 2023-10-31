package hu.bme.mit.theta.analysis.zone;

import java.util.Objects;
import java.util.Optional;

public class Pair <K, V>{
    private K key;
    private Optional<V> value;


    public Pair(K key){
        this.key = key;
        this.value = Optional.empty();
    }
    public Pair(K key, V value){
        this.key = key;
        this.value = Optional.of(value);
    }
    public K getKey(){
        return this.key;
    }
    public V getValue(){
        return this.value.get();
    }

    public boolean NoValue(){ return value.isEmpty();}

    public boolean equals(Pair p){
        if(key.equals(p.key)){
            if(value.isEmpty()) {
                if(p.value.isEmpty()) return true;
                else return false;
            }
            else{
                if(p.value.isEmpty()) return false;
                else if(value.get().equals(p.value.get())) return true;
            }
        }
        return false;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        return equals((Pair)o);
    }

    @Override
    public int hashCode() {
        return Objects.hash(key, value);
    }
}
