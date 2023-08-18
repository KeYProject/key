/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import javax.annotation.Nullable;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.HasLocation;

public class ScriptException extends Exception implements HasLocation {

    private static final long serialVersionUID = -1200219771837971833L;

    private final Location location;

    public ScriptException() {
        super();
        this.location = null;
    }

    public ScriptException(String message, Location location, Throwable cause) {
        super(message, cause);
        this.location = location;
    }

    public ScriptException(String message, Location location) {
        super(message);
        this.location = location;
    }


    public ScriptException(String message) {
        super(message);
        this.location = null;
    }

    public ScriptException(Throwable cause) {
        super(cause);
        this.location = null;
    }

    public ScriptException(String message, Throwable cause) {
        super(message, cause);
        this.location = null;
    }

    @Nullable
    @Override
    public Location getLocation() {
        return location;
    }

}
