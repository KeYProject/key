package de.uka.ilkd.key.nui.exceptions;

public class NoSearchViewAddedException extends NUIException {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    @Override
    public String getMessage() {
        return "No searchView was added.";

    }

}
