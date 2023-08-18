/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;

import java.io.Serializable;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/**
 * this class encapsulates a SchemaVariable and its corresponding instantiation if it is a
 * JavaProgramElement. The class MapFrom...cannot be used because of the different packages of the
 * SchemaVariable and the JavaProgramElement.
 */
public class ProgramSVEntry implements Serializable {

    /**
     *
     */
    private static final long serialVersionUID = -5837249343101979072L;
    /** the SchemaVariable */
    private final SchemaVariable key;
    /** the JavaProgramElement */
    private final JavaProgramElement value;

    /**
     * creates a new entry encapsulating the SchemaVariable key and its JavaProgramElement
     * instantiation value
     *
     * @param key the SchemaVariable that is instantiated
     * @param value the JavaProgramElement
     */
    public ProgramSVEntry(SchemaVariable key, JavaProgramElement value) {
        this.key = key;
        this.value = value;
    }

    /**
     * returns the SchemaVariable to be instantiated
     *
     * @return the SchemaVariable to be instantiated
     */
    public SchemaVariable key() {
        return key;
    }

    /**
     * returns true iff the keys and the mapped values are equal
     *
     * @return true iff the keys and the mapped values are equal
     */
    public boolean equals(Object o) {
        if (!(o instanceof ProgramSVEntry)) {
            return false;
        }
        final ProgramSVEntry cmp = (ProgramSVEntry) o;
        return key().equals(cmp.key()) && value().equals(cmp.value());
    }

    public int hashCode() {
        int result = 17;
        result = 37 * result + key().hashCode();
        result = 37 * result + value().hashCode();
        return result;
    }

    /**
     * returns the instantiation of the SchemaVariable
     *
     * @return the instantiation of the SchemaVariable
     */
    public JavaProgramElement value() {
        return value;
    }

    /** toString */
    public String toString() {
        return "{" + key + "<--" + value + "}";
    }

}
