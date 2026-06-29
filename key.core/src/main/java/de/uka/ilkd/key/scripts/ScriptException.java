/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import org.key_project.util.parsing.HasLocation;
import org.key_project.util.parsing.Location;

import org.jspecify.annotations.Nullable;

/// Base exception for script execution errors.
/// Carries optional location information pointing to the source of the error in the script.
///
/// @author Mattias Ulbrich
public class ScriptException extends Exception implements HasLocation {

    private static final long serialVersionUID = -1200219771837971833L;

    private final @Nullable Location location;

    public ScriptException() {
        super();
        this.location = Location.UNDEFINED;
    }

    public ScriptException(String message, Location location, Throwable cause) {
        super(message, cause);
        this.location = location;
    }

    public ScriptException(String message, @Nullable Location location) {
        super(message);
        this.location = location;
    }


    public ScriptException(String message) {
        super(message);
        this.location = Location.UNDEFINED;
    }

    public ScriptException(Throwable cause) {
        super(cause);
        this.location = Location.UNDEFINED;
    }

    public ScriptException(String message, Throwable cause) {
        super(message, cause);
        this.location = Location.UNDEFINED;
    }

    @Override
    public Location getLocation() {
        return location;
    }
}
