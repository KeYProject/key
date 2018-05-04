package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.parser.Location;

@SuppressWarnings("serial")
public class ScriptException extends Exception {

    private final Location location;

    public ScriptException() {
        super();
        this.location = null;
    }

    public ScriptException(String message, String file, int line, int col, Throwable cause) {
        super(message, cause);
        if(file != null) {
            this.location = new Location(file, line, col);
        } else {
            this.location = null;
        }
    }

    public ScriptException(String message, String file, int line, int col) {
        super(message);
        if(file != null) {
            this.location = new Location(file, line, col);
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
