package org.key_project.key4eclipse.util.java;

/**
 * Utility class to select elements.
 * @author Martin Hentschel
 */
public interface IFilter<T> {
    /**
     * Checks if the given element should be selected.
     * @param element The element to test.
     * @return {@code true} handle element, {@code false} ignore element.
     */
    public boolean select(T element);
}