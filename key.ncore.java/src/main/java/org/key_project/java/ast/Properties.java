package org.key_project.java.ast;

/**
 *
 * @author Alexander Weigl
 * @version 1 (4/12/26)
 */
public interface Properties {
    <T> T get(Property<T> property, T defaultValue);
    <T> T get(Property<T> property);
    <T> boolean contains(Property<T> property);
    <T> void set(Property<T> property, T value);
}
