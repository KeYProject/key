package org.key_project.util;

/**
 * Interface providing an equality check that actually compares object contents.
 * Some KeY classes depend on equals() being implemented as reference equality.
 *
 * @author Arne Keller
 */
public interface RealEquals {
    boolean realEquals(Object obj);
}
