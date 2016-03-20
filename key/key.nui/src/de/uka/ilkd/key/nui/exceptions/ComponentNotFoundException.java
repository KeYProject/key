package de.uka.ilkd.key.nui.exceptions;

/**
 * Exception thrown by {@link NUI#getComponent(String)} if component with the
 * given fx:id was not found.
 * 
 * @author Florian Breitfelder
 */
public class ComponentNotFoundException extends NUIException {

    /**
     * The class version number.
     */
    private static final long serialVersionUID = 1L;
    /**
     * The file which caused the exception.
     */
    private final String file;
    /**
     * TODO
     * @return
     */
    public String getFile() {
        return file;
    }
    /**
     * Creates a new ComponentNotFoundException.
     * 
     * @param file
     *            The file causing this exception.
     */
    public ComponentNotFoundException(final String file) {
        super();
        this.file = file;
    }

    @Override
    public String getMessage() {
        return "Can't load component " + file;

    }

}
