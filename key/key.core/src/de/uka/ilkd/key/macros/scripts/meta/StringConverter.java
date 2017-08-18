package de.uka.ilkd.key.macros.scripts.meta;

/**
 * @param <T>
 */
public interface StringConverter<T> {
    T convert(String s) throws Exception;
}
