

package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.common.sort.object.IteratorOfString;
import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.*;  //because the involved classes may be spread

/** this class wraps @see{java.util.HashMap} but ensures that all keys
 * are from type String and the corresponding values are StructSort types
 * The method are a subset of the java.util.HashMap so for a 
 * description see the JDK 1.2 API-Doc
 */
import java.util.HashMap;
import java.util.Iterator;

public class HashMapFromStringToStructSort implements java.io.Serializable {
    
    /** the wrapped HashMap */
    private HashMap map;

    /** creates an empty HashMap with keys of type String and values of
     * type StructSort
     */
    public HashMapFromStringToStructSort() {
	map=new HashMap();
    }

    /** used by clone, handsover a HashMap map */
    private HashMapFromStringToStructSort(HashMap map) {
	this.map=map;
    }


    /** removes all elements from this mapped */
    public void clear() {
	map.clear();
    }

    /** copies this map but without copying the keys or values */
    public Object clone() {
	return new HashMapFromStringToStructSort((HashMap)map.clone());
    }

    /** @return true iff key is mapped to one value */
    public boolean containsKey(String key) {
	return map.containsKey(key);
    }

    /** @return true iff value is mapped by one ore more keys */
    public boolean containsValue(StructSort val) {
	return map.containsValue(val);
    }

    /** @return value of StructSort that is mapped to key, null if key has no
    * mapping */
    
    public StructSort get(String key) {
	return (StructSort)map.get(key);
    }

    /** @return true iff map contains no mapping */
    public boolean isEmpty() {
	return map.isEmpty();
    }

    /** @return IteratorOfString with all keys */
    public IteratorOfString keyIterator() {
	return new HashMapKeyIterator(map);
    }

    /** adds a mappig (key,value) to this map 
     * @return value that was mapped to key before
     */
    public StructSort put(String key, StructSort val) {
	return (StructSort)map.put(key,val);
    }

    /** removes mapping for the specified key
     * @return the deleted value 
     */
    public StructSort remove(String key) {
	return (StructSort)map.remove(key);
    }

    /** @return the number of mappings */
    public int size() {
	return map.size();
    }

    /** @return IteratorOfStructSort with all values */
    public IteratorOfStructSort values() {
	return new HashMapValueIterator(map);
    }

    /** toString*/
    public String toString() {
	return map.toString();
    }

    private static class HashMapValueIterator implements IteratorOfStructSort{
	
	private Iterator it;

	private HashMapValueIterator(HashMap map) {
	    it=(map.values()).iterator();
	}

	public boolean hasNext() {
	    return it.hasNext();
	}

	public StructSort next() {
	    return (StructSort)it.next();
	}

    }

    private static class HashMapKeyIterator implements IteratorOfString{
	
	private Iterator it;

	private HashMapKeyIterator(HashMap map) {
	    it=(map.keySet()).iterator();
	}

	public boolean hasNext() {
	    return it.hasNext();
	}

	public String next() {
	    return (String)it.next();
	}

    }
}

