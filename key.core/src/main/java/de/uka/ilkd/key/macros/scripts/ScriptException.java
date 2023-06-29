package de.uka.ilkd.key.macros.scripts;

import javax.annotation.Nonnull;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.HasLocation;

public class ScriptException extends Exception implements HasLocation {

    private static final long serialVersionUID = -1200219771837971833L;

    private final Location location;

    public ScriptException() {
        super();
        this.location = Location.UNDEFINED;
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

    @Nonnull
    @Override
    public Location getLocation() {
        return location;
    }
}
