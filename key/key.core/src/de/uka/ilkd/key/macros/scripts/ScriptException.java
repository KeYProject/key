package de.uka.ilkd.key.macros.scripts;

import java.io.File;

@SuppressWarnings("serial")
public class ScriptException extends Exception {


    public ScriptException() {
        super();
    }

    public ScriptException(String message, File file, int line, Throwable cause) {
        super(message, cause);
    }

    public ScriptException(String message) {
        super(message);
    }

    public ScriptException(Throwable cause) {
        super(cause);
    }

    public ScriptException(String message, Throwable cause) {
        super(message, cause);
    }

}
