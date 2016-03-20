package de.uka.ilkd.key.nui.exceptions;

/**
 * Exception thrown by {@link NUI#getController(String)} if controller with the
 * given fx:id was not found.
 * 
 * @author Florian Breitfelder
 */
public class ControllerNotFoundException extends NUIException {

    /**
     * The class version number.
     */
    private static final long serialVersionUID = 1L;

    /**
     * The file which caused the exception.
     */
    private String file;

    /**
     * Creates a new ControllerNotFoundException.
     * 
     * @param file
     *            The file causing this exception.
     */
    public ControllerNotFoundException(final String file) {
        this.file = file;
    }

    @Override
    public String getMessage() {
        return "Can't load controller " + file;

    }

}
