

package de.uka.ilkd.key.lang.clang.common.type;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.*;  //because the involved classes may be spread

/** this class wraps @see{java.util.HashMap} but ensures that all keys
 * are from type IClangType and the corresponding values are IClangType types
 * The method are a subset of the java.util.HashMap so for a 
 * description see the JDK 1.2 API-Doc
 */
import java.util.HashMap;
import java.util.Iterator;

public class HashMapFromIClangTypeToIClangType implements java.io.Serializable {
    
    /** the wrapped HashMap */
    private HashMap map;

    /** creates an empty HashMap with keys of type IClangType and values of
     * type IClangType
     */
    public HashMapFromIClangTypeToIClangType() {
	map=new HashMap();
    }

    /** used by clone, handsover a HashMap map */
    private HashMapFromIClangTypeToIClangType(HashMap map) {
	this.map=map;
    }


    /** removes all elements from this mapped */
    public void clear() {
	map.clear();
    }

    /** copies this map but without copying the keys or values */
    public Object clone() {
	return new HashMapFromIClangTypeToIClangType((HashMap)map.clone());
    }

    /** @return true iff key is mapped to one value */
    public boolean containsKey(IClangType key) {
	return map.containsKey(key);
    }

    /** @return true iff value is mapped by one ore more keys */
    public boolean containsValue(IClangType val) {
	return map.containsValue(val);
    }

    /** @return value of IClangType that is mapped to key, null if key has no
    * mapping */
    
    public IClangType get(IClangType key) {
	return (IClangType)map.get(key);
    }

    /** @return true iff map contains no mapping */
    public boolean isEmpty() {
	return map.isEmpty();
    }

    /** @return IteratorOfIClangType with all keys */
    public IteratorOfIClangType keyIterator() {
	return new HashMapKeyIterator(map);
    }

    /** adds a mappig (key,value) to this map 
     * @return value that was mapped to key before
     */
    public IClangType put(IClangType key, IClangType val) {
	return (IClangType)map.put(key,val);
    }

    /** removes mapping for the specified key
     * @return the deleted value 
     */
    public IClangType remove(IClangType key) {
	return (IClangType)map.remove(key);
    }

    /** @return the number of mappings */
    public int size() {
	return map.size();
    }

    /** @return IteratorOfIClangType with all values */
    public IteratorOfIClangType values() {
	return new HashMapValueIterator(map);
    }

    /** toString*/
    public String toString() {
	return map.toString();
    }

    private static class HashMapValueIterator implements IteratorOfIClangType{
	
	private Iterator it;

	private HashMapValueIterator(HashMap map) {
	    it=(map.values()).iterator();
	}

	public boolean hasNext() {
	    return it.hasNext();
	}

	public IClangType next() {
	    return (IClangType)it.next();
	}

    }

    private static class HashMapKeyIterator implements IteratorOfIClangType{
	
	private Iterator it;

	private HashMapKeyIterator(HashMap map) {
	    it=(map.keySet()).iterator();
	}

	public boolean hasNext() {
	    return it.hasNext();
	}

	public IClangType next() {
	    return (IClangType)it.next();
	}

    }
}

