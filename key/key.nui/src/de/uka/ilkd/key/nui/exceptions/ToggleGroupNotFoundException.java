package de.uka.ilkd.key.nui.exceptions;

/**
 * Exception thrown by {@link NUI#getToggleGroup(String)} if toggle group with
 * the given fx:id was not found.
 * 
 * @author Florian Breitfelder
 */
public class ToggleGroupNotFoundException extends NUIException {

    /**
     * The class version number.
     */
    private static final long serialVersionUID = 1L;

    /**
     * The toggle group which could not be found.
     */
    private String toggleGroup;

    /**
     * Creates a new ToggleGroupNotFoundException.
     * 
     * @param fxId
     *            The fx:id of the toggle group which could not be found.
     */
    public ToggleGroupNotFoundException(final String fxId) {
        super();
        this.toggleGroup = fxId;
    }

    @Override
    public String getMessage() {
        return "Can't load togglegroup " + toggleGroup;

    }

    /**
     * Getter.
     * @return a {@link String} representing the the ToggleGroups fx:id.
     */
    public String getToggleGroup() {
        return toggleGroup;
    }

    /**
     * Setter.
     * @param toggleGroup a {@link String} representing the the ToggleGroups fx:id.
     */
    public void setToggleGroup(final String toggleGroup) {
        this.toggleGroup = toggleGroup;
    }

}
