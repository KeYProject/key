package org.key_project.util;

/**
 * Interface to check object equality modulo factors that are not relevant to the proof
 * (e.g., origin labels).
 *
 * @author Arne Keller
 */
public interface EqualsModProofIrrelevancy {
    /**
     * Checks whether this object and the other object represent the same data, whilst ignoring
     * attributes that are not relevant for the purpose of these objects in the proof.
     *
     * @param obj other object
     * @return whether these objects are equal
     */
    boolean equalsModProofIrrelevancy(Object obj);

    /**
     * Compute a hashcode that represents the proof-relevant fields of this object.
     *
     * @return the hashcode
     */
    int hashCodeModProofIrrelevancy();
}
