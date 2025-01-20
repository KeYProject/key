/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.QuantifiableVariable;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableMap;

public class RenameTable {

    public static final RenameTable EMPTY_TABLE = new EmptyRenameTable();

    /**
     * local map mapping a QuantifiableVariable object to an abstract name. This map is allowed to
     * hide bound renaming of the parent table.
     */
    private final ImmutableMap<QuantifiableVariable, Integer> localRenamingTable;

    /**
     * the maximal value of an abstract name
     */
    private final int max;

    /** the parent renaming table */
    private final RenameTable parent;


    public RenameTable(RenameTable parent, ImmutableMap<QuantifiableVariable, Integer> localTable,
            int newMax) {
        this.parent = parent;
        this.localRenamingTable = localTable;
        max = newMax;
    }

    /**
     * returns true iff the given variable is mapped to an abstract name. The test is performed in
     * the local as well as in the parent renaming table.
     *
     * @param n the QuantifiableVariable object the existence of an abstract name is checked.
     * @return true if <code>n</code> has been already assigned to an abstract name
     */
    public boolean contains(QuantifiableVariable n) {
        return localRenamingTable.containsKey(n) || parent.contains(n);
    }

    /**
     * does nearly the same as {@link #contains(QuantifiableVariable)} but performs the test only on
     * the local table
     *
     * @param n the QuantifiableVariable object the existence of an abstract name is checked.
     * @return true if <code>n</code> has been already locally assigned to an abstract name
     */
    public boolean containsLocally(QuantifiableVariable n) {
        return localRenamingTable.containsKey(n);
    }

    /**
     * tests if both QuantifiableVariables are assigned to the same abstract name (locally or by the
     * parent)
     *
     * @param n1 one of the QuantifiableVariables to be tested iff they have been assigned the same
     *        abstract name
     * @param n2 one of the QuantifiableVariables to be tested
     * @return true iff <code>n1</code> and <code>n2</code> are mapped to the same abstract name
     */
    public boolean sameAbstractName(QuantifiableVariable n1, QuantifiableVariable n2) {
        if (containsLocally(n1)) {
            return localRenamingTable.get(n1).equals(localRenamingTable.get(n2));
        } else {
            return parent.sameAbstractName(n1, n2);
        }
    }


    private Integer createNewAbstractName() {
        if (max == Integer.MAX_VALUE) {
            throw new IllegalStateException("Overflow in renaming table. Why on earth "
                + "are there " + Integer.MAX_VALUE + " + 1 variables to be renamed?");
        }

        return max + 1;
    }

    /**
     * assigns both QuantifiableVariable objects the same abstract name
     */
    public RenameTable assign(QuantifiableVariable n1, QuantifiableVariable n2) {
        final Integer newAbstractName = createNewAbstractName();
        return new RenameTable(parent,
            localRenamingTable.put(n1, newAbstractName).put(n2, newAbstractName),
            newAbstractName);
    }

    /**
     * creates a nested renaming table with <code>this</code> as parent
     */
    public RenameTable extend() {
        return new RenameTable(this, DefaultImmutableMap.nilMap(), createNewAbstractName());
    }


    /**
     * toString
     */
    public String toString() {
        return localRenamingTable + " \n parent:" + parent;
    }


    private static class EmptyRenameTable extends RenameTable {

        private EmptyRenameTable() {
            super(null, DefaultImmutableMap.nilMap(), 0);
        }

        /**
         * returns true iff the given name is mapped to an abstract name. The test is performed in
         * the local as well as in the parent renaming table.
         *
         * @param n the QuantifiableVariable object the existence of an abstract name is checked.
         * @return true if <code>n</code> has been already assigned to an abstract name
         */
        public boolean contains(QuantifiableVariable n) {
            return false;
        }

        /**
         * does nearly the same as {@link #contains(QuantifiableVariable)} but performs the test
         * only on the local table-
         *
         * @param n the QuantifiableVariable object the existence of an abstract name is checked.
         * @return true if <code>n</code> has been already locally assigned to an abstract name
         */
        public boolean containsLocally(QuantifiableVariable n) {
            return false;
        }

        /**
         * tests if both QuantifiableVariable object are assigned to the same abstract name (locally
         * or by the parent)
         *
         * @param n1 one of the QuantifiableVariable objects to be tested iff they have been
         *        assigned the same abstract name
         * @param n2 one of the QuantifiableVariable objects to be tested
         * @return true iff <code>n1</code> and <code>n2</code> are mapped to the same abstract name
         */
        public boolean sameAbstractName(QuantifiableVariable n1, QuantifiableVariable n2) {
            return false;
        }


        public String toString() {
            return "empty";
        }
    }

    public RenameTable parent() {
        return parent;
    }
}
