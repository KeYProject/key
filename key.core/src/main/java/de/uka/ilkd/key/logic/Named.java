package de.uka.ilkd.key.logic;

/**
 * This interface has to be implemented by all logic signature elements, which are identified by
 * their name.
 */
public interface Named {

    /**
     * returns the name of this element
     *
     * @return the name of the element
     */
    Name name();

}
