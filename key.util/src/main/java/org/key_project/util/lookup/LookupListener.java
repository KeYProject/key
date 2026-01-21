package org.key_project.util.lookup;

/**
 * @author Alexander Weigl
 * @version 1 (15.03.19)
 */
public interface LookupListener {
    void update(Class<?> clazz, Lookup lookup);
}
