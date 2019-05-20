package de.uka.ilkd.key.gui.prooftree;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.19)
 */
public interface Styler<T> {
    void style(Style current, T obj);
}
