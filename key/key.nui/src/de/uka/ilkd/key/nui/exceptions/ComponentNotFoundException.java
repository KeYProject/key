package de.uka.ilkd.key.nui.exceptions;

public class ComponentNotFoundException extends NUIException {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;
    
    private String file;

    public ComponentNotFoundException(String file) {
        this.file = file;
    }

    @Override
    public String getMessage() {
        return "Can't load component " + file;

    }

}
