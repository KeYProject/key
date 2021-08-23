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
    @Nullable
    Location getLocation() throws MalformedURLException;
}
