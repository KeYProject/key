/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;


import org.key_project.util.parsing.HasLocation;
import org.key_project.util.parsing.Location;

import com.github.javaparser.ast.Node;

/**
 * This exception class is mainly thrown by Recoder2KeY and its companions.
 *
 * It stores its reason not only by the cause mechanism of Exceptions but also separately if it is a
 * parser error.
 *
 * This information is then read by the KeYParser to produce helpful error messages.
 *
 */
public class ConvertException extends RuntimeException implements HasLocation {
    private final Location location;

    public ConvertException(String message) {
        super(message);
        location = Location.UNDEFINED;
    }

    public ConvertException(String message, Location location) {
        super(message);
        this.location = location;
    }

    /**
     * Create a conversion exception that points to the source location of the given JavaParser
     * node. This helps the user to locate the origin of the conversion problem in the input file.
     *
     * @param message the error message
     * @param node the JavaParser node the conversion failed on
     */
    public ConvertException(String message, Node node) {
        this(message, JavaSourceLocations.locationFromNode(node));
    }

    @Override
    public Location getLocation() {
        return location;
    }

    @Override
    public String getMessage() {
        // Only append the location if it actually carries information; otherwise the
        // bare "[<unknown>:??]" suffix just clutters the message.
        if (location == null || location.equals(Location.UNDEFINED)) {
            return super.getMessage();
        }
        return super.getMessage() + "\n" + location;
    }
}
