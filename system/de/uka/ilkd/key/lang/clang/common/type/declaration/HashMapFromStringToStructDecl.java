

package de.uka.ilkd.key.lang.clang.common.type.declaration;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.*;  //because the involved classes may be spread

/** this class wraps @see{java.util.HashMap} but ensures that all keys
 * are from type String and the corresponding values are StructDecl types
 * The method are a subset of the java.util.HashMap so for a 
 * description see the JDK 1.2 API-Doc
 */
import java.util.HashMap;
import java.util.Iterator;

public class HashMapFromStringToStructDecl implements java.io.Serializable {
    
    /** the wrapped HashMap */
    private HashMap map;

    /** creates an empty HashMap with keys of type String and values of
     * type StructDecl
     */
    public HashMapFromStringToStructDecl() {
	map=new HashMap();
    }

    /** used by clone, handsover a HashMap map */
    private HashMapFromStringToStructDecl(HashMap map) {
	this.map=map;
    }


    /** removes all elements from this mapped */
    public void clear() {
	map.clear();
    }

    /** copies this map but without copying the keys or values */
    public Object clone() {
	return new HashMapFromStringToStructDecl((HashMap)map.clone());
    }

    /** @return true iff key is mapped to one value */
    public boolean containsKey(String key) {
	return map.containsKey(key);
    }

    /** @return true iff value is mapped by one ore more keys */
    public boolean containsValue(StructDecl val) {
	return map.containsValue(val);
    }

    /** @return value of StructDecl that is mapped to key, null if key has no
    * mapping */
    
    public StructDecl get(String key) {
	return (StructDecl)map.get(key);
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
    public StructDecl put(String key, StructDecl val) {
	return (StructDecl)map.put(key,val);
    }

    /** removes mapping for the specified key
     * @return the deleted value 
     */
    public StructDecl remove(String key) {
	return (StructDecl)map.remove(key);
    }

    /** @return the number of mappings */
    public int size() {
	return map.size();
    }

    /** @return IteratorOfStructDecl with all values */
    public IteratorOfStructDecl values() {
	return new HashMapValueIterator(map);
    }

    /** toString*/
    public String toString() {
	return map.toString();
    }

    private static class HashMapValueIterator implements IteratorOfStructDecl{
	
	private Iterator it;

	private HashMapValueIterator(HashMap map) {
	    it=(map.values()).iterator();
	}

	public boolean hasNext() {
	    return it.hasNext();
	}

	public StructDecl next() {
	    return (StructDecl)it.next();
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

