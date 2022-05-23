package org.key_project.util.java;

/**
 * Utility class to select elements which also allows that exceptions
 * are thrown during selection phase.
 * @author Martin Hentschel
 */
public interface IFilterWithException<T, E extends Throwable> {
    /**
     * Checks if the given element should be selected.
     * @param element The element to test.
     * @return {@code true} handle element, {@code false} ignore element.
     * @throws E An occurred exception.
     */
    public boolean select(T element) throws E;
}