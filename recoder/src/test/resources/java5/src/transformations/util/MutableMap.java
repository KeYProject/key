
package recoder.util;

/**
 * @author AL
 */
public interface MutableMap extends Map {

    Object put(Object key, Object value);

    Object remove(Object key);

    void clear();
}