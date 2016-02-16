package de.uka.ilkd.key.nui.exceptions;

public class ToggleGroupNotFoundException extends NUIException {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    private String toggleGroup;

    public ToggleGroupNotFoundException(String file) {
        this.toggleGroup = file;
    }

    @Override
    public String getMessage() {
        return "Can't load togglegroup " + toggleGroup;

    }

}
