package de.uka.ilkd.key.macros.scripts.meta;

/**
 * @param <T>
 */
public interface Converter<T> {
    T convert(String s) throws Exception;
}
