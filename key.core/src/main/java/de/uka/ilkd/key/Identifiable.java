package de.uka.ilkd.key;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.23)
 */
public interface Identifiable {
    default String identification() {
        return getClass().getName() + "_" + hashCode();
    }
}
