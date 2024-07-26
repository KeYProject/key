package org.key_project.rusty.logic.equality;

public interface Property<T> {
    /**
     * Checks {@code t1} and {@code t2} for equality ignoring a certain property.
     *
     * @param t1 the first element of the equality check
     * @param t2 the second element of the equality check
     * @param v the additional arguments needed for the equality check
     * @return whether {@code t1} and {@code t2} are equal ignoring a certain property
     * @param <V> the type of the additional parameters needed for the comparison
     */
    <V> boolean equalsModThisProperty(T t1, T t2, V... v);

    /**
     * Computes the hash code of {@code t} in a context where
     * {@link this#equalsModThisProperty(Object, Object, Object[])}
     * is used as an equality check, so that it can be used in, e.g., a HashMap.
     *
     * @param t the object to compute the hash code for
     * @return the hash code of {@code t} ignoring a certain property
     */
    int hashCodeModThisProperty(T t);
}
