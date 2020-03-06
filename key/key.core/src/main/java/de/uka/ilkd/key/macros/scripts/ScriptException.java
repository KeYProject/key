package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.parser.Location;

import java.net.URL;

public class ScriptException extends Exception {

    private static final long serialVersionUID = -1200219771837971833L;

    private final Location location;

    public ScriptException() {
        super();
        this.location = null;
    }

    public ScriptException(String message, URL url, int line, int col, Throwable cause) {
        super(message, cause);
        if(url != null) {
            this.location = new Location(url, line, col);
        } else {
            this.location = null;
        }
    }

    public ScriptException(String message, URL url, int line, int col) {
        super(message);
        if(url != null) {
            this.location = new Location(url, line, col);
        } else {
            this.location = null;
        }
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

    public Location getLocation() {
        return location;
    }

}
