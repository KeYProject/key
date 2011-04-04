package de.uka.ilkd.key.util;

import java.util.Iterator;

public class LinkedHashMap<K, V>
	extends java.util.LinkedHashMap<K, V> {

    /**
     * 
     */
    private static final long serialVersionUID = -6216276580053259582L;
    
    
    public LinkedHashMap() {
	super();
    }
    
    
    public LinkedHashMap(K key, V value) {
	super();
	put(key, value);
    }
    
    
    public LinkedHashMap(K[] keys, V[] values) {
	super();
	putAll(keys, values);
    }
    
    
    public LinkedHashMap(Iterable<K> keys, Iterable<V> values) {
	super();
	putAll(keys, values);
    }
    
    
    public void putAll(K[] keys, V[]vals) {
	for (int i = 0; i < keys.length; i++) {
	    if (i < vals.length) {
		put(keys[i], vals[i]);
	    } else {
		put(keys[i], null);
	    }
	}
    }

    
    public void putAll(Iterable<K> keys, Iterable<V> vals) {
	Iterator<V> itVals = vals.iterator();
	for (K key : keys) {
	    if (itVals.hasNext()) {
		put(key, itVals.next());
	    } else {
		put(key, null);
	    }
	}
    }
    
}
