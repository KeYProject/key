

package de.uka.ilkd.key.lang.clang.common.sort.object;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.*;  //because the involved classes may be spread

/** this class wraps @see{java.util.HashMap} but ensures that all keys
 * are from type String and the corresponding values are MemberInfo types
 * The method are a subset of the java.util.HashMap so for a 
 * description see the JDK 1.2 API-Doc
 */
import java.util.HashMap;
import java.util.Iterator;

public class HashMapFromStringToMemberInfo implements java.io.Serializable {
    
    /** the wrapped HashMap */
    private HashMap map;

    /** creates an empty HashMap with keys of type String and values of
     * type MemberInfo
     */
    public HashMapFromStringToMemberInfo() {
	map=new HashMap();
    }

    /** used by clone, handsover a HashMap map */
    private HashMapFromStringToMemberInfo(HashMap map) {
	this.map=map;
    }


    /** removes all elements from this mapped */
    public void clear() {
	map.clear();
    }

    /** copies this map but without copying the keys or values */
    public Object clone() {
	return new HashMapFromStringToMemberInfo((HashMap)map.clone());
    }

    /** @return true iff key is mapped to one value */
    public boolean containsKey(String key) {
	return map.containsKey(key);
    }

    /** @return true iff value is mapped by one ore more keys */
    public boolean containsValue(MemberInfo val) {
	return map.containsValue(val);
    }

    /** @return value of MemberInfo that is mapped to key, null if key has no
    * mapping */
    
    public MemberInfo get(String key) {
	return (MemberInfo)map.get(key);
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
    public MemberInfo put(String key, MemberInfo val) {
	return (MemberInfo)map.put(key,val);
    }

    /** removes mapping for the specified key
     * @return the deleted value 
     */
    public MemberInfo remove(String key) {
	return (MemberInfo)map.remove(key);
    }

    /** @return the number of mappings */
    public int size() {
	return map.size();
    }

    /** @return IteratorOfMemberInfo with all values */
    public IteratorOfMemberInfo values() {
	return new HashMapValueIterator(map);
    }

    /** toString*/
    public String toString() {
	return map.toString();
    }

    private static class HashMapValueIterator implements IteratorOfMemberInfo{
	
	private Iterator it;

	private HashMapValueIterator(HashMap map) {
	    it=(map.values()).iterator();
	}

	public boolean hasNext() {
	    return it.hasNext();
	}

	public MemberInfo next() {
	    return (MemberInfo)it.next();
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

