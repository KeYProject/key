/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.parsing;

import java.net.MalformedURLException;
import javax.annotation.Nullable;

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
     * @throws MalformedURLException if the URL for the location can not be created
     */
    @Nullable
    Location getLocation() throws MalformedURLException;
}
