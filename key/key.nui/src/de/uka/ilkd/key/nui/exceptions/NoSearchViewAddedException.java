package de.uka.ilkd.key.nui.exceptions;

/**
 * Exception thrown by {@link TreeViewController#openSearchView()} if the
 * searchView was never added before, see
 * {@link TreeViewController#addSearchView(SearchPane, SearchViewController)}.
 * 
 * @author Florian Breitfelder
 *
 */
public class NoSearchViewAddedException extends NUIException {

    /**
     * The class version number.
     */
    private static final long serialVersionUID = 1L;

    @Override
    public String getMessage() {
        return "No searchView was added before.";

    }

}
