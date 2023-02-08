package de.uka.ilkd.key.logic;


/** implemented by iterators of primitive type int */
public interface IntIterator {

    /** @return Integer the next element of collection */
    int next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}
