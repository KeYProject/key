package de.uka.ilkd.key.macros.scripts.meta;

/**
 * A {@link StringConverter} translates a textual representation
 * to an instance of {@code T}.
 *
 * @param <T>
 * @author Alexander Weigl
 */
public interface StringConverter<T> {
    /**
     * Translates the textual representation given in {@code s} to an instance of {@code T}.
     *
     * @param s a non-null string
     * @return an corresponding instance of T
     * @throws Exception if there is an error during the translation (format incorrent etc..)
     */
    T convert(String s) throws Exception;
}
