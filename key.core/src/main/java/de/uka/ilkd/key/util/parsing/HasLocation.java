package de.uka.ilkd.key.util.parsing;

import de.uka.ilkd.key.parser.Location;

import javax.annotation.Nullable;
import java.net.MalformedURLException;

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
     * @throws MalformedURLException if the URL for the location can not be created
     */
    @Nullable
    Location getLocation() throws MalformedURLException;
}
