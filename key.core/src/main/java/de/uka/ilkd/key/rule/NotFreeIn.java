/**
 * class contains a pair of SchemaVariables, the first part has to be match a QuantifiableVariable,
 * the second one a Term in order to model a pair of the not-free-in relation of an Taclet.
 */

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.VariableSV;

public class NotFreeIn {

    private final SchemaVariable first;
    private final SchemaVariable second;

    /**
     * constructs a pair of variables given two SchemaVariables. The first SchemaVariable has to
     * occur bound in the Taclet, while the second one can stand for a an arbitrary term of formula,
     * in order to model a pair of the not-free-in relation of an Taclet.
     */
    public NotFreeIn(SchemaVariable first, SchemaVariable second) {
        if (!(first instanceof VariableSV)) {
            throw new RuntimeException("Expected a SchemaVariable "
                + "that has been only allowed to match " + "variables");
        }
        this.first = first;
        this.second = second;
    }

    /**
     * returns the first SchemaVariable of the pair. This SchemaVariable has to be matched to a
     * QuantifiableVariable
     */
    public SchemaVariable first() {
        return first;
    }

    /** returns the second SchemaVariable of the pair. */
    public SchemaVariable second() {
        return second;
    }

    public String toString() {
        return "\\notFreeIn(" + first() + "," + second() + ")";
    }

    public boolean equals(Object o) {
        if (!(o instanceof NotFreeIn)) {
            return false;
        }
        NotFreeIn nfi = (NotFreeIn) o;
        return nfi.first == first() && nfi.second == second();
    }

    public int hashCode() {
        int result = 17;
        result = 37 * result + first().hashCode();
        result = 37 * result + second().hashCode();
        return result;
    }
}
