public class Entry {

    /**
     * Holds the next node.
     */
    Entry /*@nullable@*/ _next;

    /**
     * Holds the previous node.
     */
    Entry _previous;

    /**
     * Holds the entry key.
     */
    Object /*{K}*/ _key;

    /**
     * Holds the entry value.
     */
    Object /*{V}*/ _value;

    /**
     * Holds the next entry in the same bucket.
     */
    Entry _beside;

    /**
     * Holds the hash table this entry belongs to.
     */
    Entry/*<K,V>*/[][] _table;

    /**
     * Holds the key hash code.
     */
    int _keyHash;

}
