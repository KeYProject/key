package de.uka.ilkd.key.gui.settings;

public interface Validator<T> {
    void validate(T obj) throws Exception;
}
