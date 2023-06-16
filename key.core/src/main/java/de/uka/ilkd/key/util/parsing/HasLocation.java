package de.uka.ilkd.key.util.parsing;


import de.uka.ilkd.key.parser.Location;

/**
 * This interface simply states, that an exception has locational information.
 *
 * @author Alexander Weigl
 * @version 1 (6/2/21)
 */
public interface HasLocation {
    /**
     * This method can be used to obtain the Location (1-based line and column!) of the exception.
     *
     * @return the location of the exception
     */
    Location getLocation();
}
