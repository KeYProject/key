package de.uka.ilkd.key.logic;

/**
 * This interface defines the basic functionalities of services
 * required to construct {@link Term}s.
 * @author Richard Bubel
 */
public interface TermServices {

    /**
     * returns the namespaces for functions, predicates etc.
     * @return the proof specific namespaces
     */
    public abstract NamespaceSet getNamespaces();

    /**
     * Returns the {@link TermBuilder} used to create {@link Term}s.
     * @return The {@link TermBuilder} used to create {@link Term}s.
     */
    public abstract TermBuilder getTermBuilder();

    /**
     * Returns the {@link TermBuilder} used to create {@link Term}s.
     * @return The {@link TermBuilder} used to create {@link Term}s.
     */
    public abstract TermFactory getTermFactory();

}