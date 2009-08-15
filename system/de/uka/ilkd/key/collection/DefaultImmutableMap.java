package de.uka.ilkd.key.collection;

import java.util.Iterator;

/**
 * This class implements ImmMap<S,T> and provides a
 * persistent Map. It is a simple implementation like lists     
 */
public class DefaultImmutableMap<S,T> implements ImmutableMap<S,T> {

    /** the empty map*/
    private static final NILMap EMPTY_MAP=new NILMap();   

    public static <S,T> DefaultImmutableMap<S,T> nilMap() {
	return EMPTY_MAP;
    }

    private final DefaultImmutableMap<S,T> parent;

    /** list of pairs (key,value) */
    private final ImmutableMapEntry<S,T> entry;

    private int hashCode = 0;

    /** only for use by NILMap */
    private DefaultImmutableMap() {
	entry       = null;
	this.parent = null;
    }


    /** creates new map with mapping entry */
    private DefaultImmutableMap(ImmutableMapEntry<S,T> entry) {
	if (entry == null)
	    throw new RuntimeException("Invalid entry");
	this.entry = entry;
	this.parent = this.<S,T>nilMap();
    }

    /** creates new map with mapping entry and parent map */
    private DefaultImmutableMap(ImmutableMapEntry<S,T> entry, DefaultImmutableMap<S,T> parent) {
	if (entry == null)
	    throw new RuntimeException("Invalid entry");
	this.entry = entry;
	this.parent = parent;
    }


    /**      
     * inserts mapping <key,val> into the map (old map is not modified) 
     * if key exists old entry has to be removed 
     * @param key a S to be used as key 
     * @param value a T to be stored as value
     * @return a ImmMap<S,T> including the <key, value> pair and all
     * other pairs of the current map with keys different from the given
     * key
     */
    public ImmutableMap<S,T> put(S key,T value) {
	return new DefaultImmutableMap<S,T>(new MapEntry<S,T>(key,value), this.remove(key));
    }



    /** @return value of type T that is mapped by key of type S */
    public T get(S key) {
	DefaultImmutableMap<S,T> queue = this;
	while (!queue.isEmpty()) {
	    final ImmutableMapEntry<S,T> e = queue.entry;

	    final S entryKey = e.key();
	    if (entryKey == key || entryKey.equals(key)) {
		return e.value();
	    }

	    queue = queue.parent;
	}
	return null;
    }

    /** @return number of entries as int */
    public int size() {
	return 1 + parent.size();
    }

    /** returns true if the map is empty */
    public boolean isEmpty() {
	return false;
    }

    /** @return true iff the map includes key */
    public boolean containsKey(S key) {
	DefaultImmutableMap<S,T> queue = this;
	while (!queue.isEmpty()) {
	    final ImmutableMapEntry<S,T> e = queue.entry;
	    final S entryKey = e.key();
	    if (entryKey == key || entryKey.equals(key)) {
		return true;
	    }

	    queue = queue.parent;
	}
	return false;
    }

    /** @return true iff the map includes value */
    public boolean containsValue(T value) {
	DefaultImmutableMap<S,T> queue = this;
	while (!queue.isEmpty()) {
	    final ImmutableMapEntry<S,T> e = queue.entry;
	    final T entryVal = e.value();
	    if (entryVal == value || entryVal.equals(value)) {
		return true;
	    }
	    queue = queue.parent;

	}
	return false;
    }

    private DefaultImmutableMap<S,T> createMap(ImmutableMapEntry<S,T>[] stack,
	    int counter,
	    DefaultImmutableMap<S,T> p_parent) {
	DefaultImmutableMap<S,T> result = p_parent;
	for (int i = 0; i<counter; i++) {
	    result = new DefaultImmutableMap<S,T>(stack[i], result);
	}
	return result;
    }

    /** 
     * removes mapping (key,...) from map
     * @return the new map (the same if key is not in the map)
     */
    public DefaultImmutableMap<S,T> remove(S key) {
	DefaultImmutableMap<S,T> queue = this;
	final ImmutableMapEntry<S,T>[] stack = new ImmutableMapEntry[size()];
	int counter = 0;
	while (!queue.isEmpty()) {
	    final ImmutableMapEntry<S,T> e = queue.entry;

	    final S entryKey = e.key();

	    if (entryKey == key || entryKey.equals(key)) {
		return createMap(stack, counter, queue.parent);
	    }


	    stack[counter] = e;
	    counter ++;

	    queue = queue.parent;
	}
	return this;
    }

    /** removes all mappings (...,value) from map
     * @return the new map (the same if value is not mapped)
     */
    public ImmutableMap<S,T> removeAll(T value) {
	DefaultImmutableMap<S,T> queue = this;
	final ImmutableMapEntry<S,T>[] stack = new ImmutableMapEntry[size()];
	int counter = 0;
	while (!queue.isEmpty()) {
	    final ImmutableMapEntry<S,T> e = queue.entry;

	    final T entryVal = e.value();

	    if (entryVal != value && !entryVal.equals(value)) {
		stack[counter] = e;
		counter ++;		
	    }

	    queue = queue.parent;

	}
	return counter < stack.length ? 
		createMap(stack, counter, this.<S,T>nilMap()) : this;
    }

    /** @return iterator for all keys */
    public Iterator<S> keyIterator() {
	return new MapKeyIterator(this);
    }

    /** @return iterator for all values */
    public Iterator<T> valueIterator() {
	return new MapValueIterator(this);
    }

    /** @return iterator for entries */
    public Iterator<ImmutableMapEntry<S,T>> entryIterator() {
	return new MapEntryIterator(this);
    }

    public String toString() {
	final StringBuffer sb = new StringBuffer("[");
	final Iterator<ImmutableMapEntry<S,T>> it = entryIterator();
	while (it.hasNext()) {
	    sb.append(""+it.next());
	    if (it.hasNext()) {
		sb.append(",");		
	    }
	}
	sb.append("]");
	return sb.toString();
    }

    public boolean equals(Object o) {
	if ( ! ( o instanceof ImmutableMap ) )
	    return false;
	if (o == this) {
	    return true;
	}

	final ImmutableMap<S,T> o1 = (ImmutableMap<S,T>)o;
	if ( o1.size() != size() )
	    return false;


	final Iterator<ImmutableMapEntry<S,T>> p = entryIterator();
	while ( p.hasNext() ) {
	    final ImmutableMapEntry<S,T> e = p.next();
	    if ( !e.value().equals(o1.get(e.key())) ) {
		return false;
	    }
	}

	return true;
    }

    public int hashCode() {
	if ( hashCode == -1 ) {
	    final Iterator<ImmutableMapEntry<S,T>> p = entryIterator();
	    while ( p.hasNext() ) {
		hashCode += 17*p.next().hashCode();
	    }
	    hashCode = hashCode == 0 ? 1 : hashCode; 
	}
	return hashCode;
    }

    /** the empty map */
    private static class NILMap<S,T> extends DefaultImmutableMap<S,T>{

	private NILMap() {
	}

	public ImmutableMap<S,T> put(S key, T value) {
	    return new DefaultImmutableMap<S,T>(new MapEntry<S,T>(key,value));
	}

	public T get(S key) {
	    return null;
	}

	public boolean isEmpty() {
	    return true;
	}

	public boolean containsKey(S key) {
	    return false;
	}

	public boolean containsValue(T val) {
	    return false;
	}

	public DefaultImmutableMap<S, T> remove(S key) {
	    return this;
	}

	public ImmutableMap<S,T> removeAll(T value) {
	    return this;
	}

	/** @return iterator for keys */
	public Iterator<S> keyIterator() {
	    return ImmutableSLList.<S>nil().iterator();
	}

	/** @return iterator for values */
	public Iterator<T> valueIterator() {
	    return ImmutableSLList.<T>nil().iterator();
	}

	/** @return iterator for entries */
	public Iterator<ImmutableMapEntry<S,T>> entryIterator() {
	    return ImmutableSLList.<ImmutableMapEntry<S,T>>nil().iterator();
	}

	public int size(){
	    return 0;
	}

	public String toString() {
	    return "[(,)]";
	}
    }

    /** inner class for the entries */
    static class MapEntry<S,T> implements ImmutableMapEntry<S,T> {
	// the key
	private final S key;
	// the value
	private final T value;

	/** creates a new map entry that contains key and value */ 
	MapEntry(S key, T value) {
	    this.key   = key;
	    this.value = value;
	} 

	/** @return the key stored in this entry */
	public S key() {
	    return key;
	}

	/** @return the value stored in this entry */
	public T value() {
	    return value;
	}	

	/** @return true iff both objects have equal pairs of key and
	 * value 
	 */ 
	public boolean equals(Object obj) {
	    final ImmutableMapEntry<S,T> cmp = (ImmutableMapEntry<S,T>) obj;
	    final S cmpKey = cmp.key();
	    final T cmpVal = cmp.value();
	    return (key == cmpKey && value == cmpVal) ||
	    (key.equals(cmpKey) && value.equals(cmpVal));
	}

	public int hashCode() {
	    return key.hashCode() * 7 + value.hashCode();
	}

	public String toString() {
	    return key+"->"+value;
	}
    }

    /** iterator for the values */
    private static abstract class MapIterator<S,T> {
	// stores the entry iterator
	private DefaultImmutableMap<S,T> map;

	// creates the iterator
	MapIterator(DefaultImmutableMap<S,T> map) {
	    this.map = map;
	}

	/** @return true iff there are more elements */
	public boolean hasNext() {
	    return !map.isEmpty();
	}

	/** @return next value in list */
	public ImmutableMapEntry<S,T> nextEntry() {
	    final DefaultImmutableMap<S,T> oldmap = map;
	    map = oldmap.parent;
	    return oldmap.entry;
	}

	/** 
	 * throws an unsupported operation exception as removing elements
	 * is not allowed on immutable maps
	 */
	public void remove() {
	    throw new UnsupportedOperationException("Removing elements via an iterator" +
	    " is not supported for immutable maps.");
	} 
    }

    /** iterator for the values */
    private class MapEntryIterator extends MapIterator<S,T>
    implements Iterator<ImmutableMapEntry<S,T>> {

	MapEntryIterator(DefaultImmutableMap<S,T> map) {
	    super(map);
	}

	/** @return next value in list */
	public ImmutableMapEntry<S,T> next() {
	    return nextEntry();
	}
    }


    private class MapValueIterator extends MapIterator<S,T> 
    implements Iterator<T> {

	MapValueIterator(DefaultImmutableMap<S,T> map) {
	    super(map);
	}

	/** @return next value in list */
	public T next() {
	    return nextEntry().value();
	}
    }

    private class MapKeyIterator extends MapIterator<S,T> 
    implements Iterator<S> {

	MapKeyIterator(DefaultImmutableMap<S,T> map) {
	    super(map);
	}

	/** @return next value in list */
	public S next() {
	    return nextEntry().key();
	}
    }
}
