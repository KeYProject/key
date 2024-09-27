/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.equality;

import java.util.HashMap;
import java.util.Map;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.SyntaxElementCursor;
import org.key_project.rusty.ast.Identifier;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.pat.IdentPattern;
import org.key_project.rusty.logic.NameAbstractionTable;
import org.key_project.rusty.logic.op.ProgramVariable;

public class RenamingProgramElementProperty implements Property<RustyProgramElement> {
    /**
     * The single instance of this property.
     */
    public static final RenamingProgramElementProperty RENAMING_PROGRAM_ELEMENT_PROPERTY =
        new RenamingProgramElementProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed through
     * {@link RenamingProgramElementProperty#RENAMING_PROGRAM_ELEMENT_PROPERTY}.
     */
    private RenamingProgramElementProperty() {}

    /**
     * Checks if {@code rpe2} is a {@link RustyProgramElement} syntactically equal to {@code rpe1}
     * modulo
     * renaming.
     * <p>
     * When this method is supplied with a {@link NameAbstractionTable}, it will use this table to
     * compare the abstract names of the source elements. If no {@link NameAbstractionTable} is
     * supplied, a new one will be created.
     *
     * @param rpe1 the first element of the equality check
     * @param rpe2 the second element of the equality check
     * @param v can be a single {@link NameAbstractionTable} for this equality check
     * @return {@code true} iff {@code rpe2} is a source element syntactically equal to {@code rpe1}
     *         modulo renaming
     * @param <V> is supposed to be {@link NameAbstractionTable} for this equality check
     */
    @Override
    public <V> boolean equalsModThisProperty(RustyProgramElement rpe1, RustyProgramElement rpe2,
            V... v) {
        NameAbstractionTable nat;
        if (v.length > 0 && (v[0] instanceof NameAbstractionTable n)) {
            nat = n;
        } else {
            nat = new NameAbstractionTable();
        }

        SyntaxElementCursor c1 = rpe1.getCursor(), c2 = rpe2.getCursor();
        SyntaxElement next1, next2;
        boolean hasNext1, hasNext2; // Check at the end if both cursors have reached the end

        do {
            // First nodes can never be null as cursor is initialized with 'this'
            next1 = c1.getCurrentNode();
            next2 = c2.getCurrentNode();
            if (next1 instanceof IdentPattern ip) {
                if (!handleIdentPattern(ip, next2, nat)) {
                    return false;
                }
            } else if (next1 instanceof ProgramVariable || next1 instanceof Identifier) {
                if (!handleProgramVariableOrIdentifier(next1, next2, nat)) {
                    return false;
                }
            } else if (next1.getChildCount() > 0) {
                if (!handleRustyNonTerminalProgramElement(next1,
                    next2)) {
                    return false;
                }
            } else {
                if (!handleStandard(next1, next2)) {
                    return false;
                }
            }
            // walk to the next nodes in the tree
        } while ((hasNext1 = c1.goToNext()) & (hasNext2 = c2.goToNext()));

        return hasNext1 == hasNext2;
    }

    // TODO: hashCodeModThisProperty currently does not take a NameAbstractionTable as an argument.
    // This is because the current implementation of hashCodeModThisProperty is not parameterized
    // with a vararg. Variables occurring in multiple formulas and RustyBlocks are considered in
    // isolation as a newly created NameAbstractionTable that does not contain entries from previous
    // RustyBlocks is used. This could possibly lead to more collisions but if this is a concern,
    // the
    // method can be changed to also take a generic vararg. That way, the NameAbstractionTable can
    // be passed to the method and hash codes can take previous usage of variables into account.
    @Override
    public int hashCodeModThisProperty(RustyProgramElement RustyProgramElement) {
        /*
         * Currently, the best approach seems to be to walk through the RustyProgramElement with a
         * SyntaxElementCursor and sum up hash codes.
         */
        // TODO: change hashCode to reflect the equalsModThisProperty method
        NameAbstractionMap absMap = new NameAbstractionMap();

        int hashCode = 1;
        SyntaxElementCursor c = RustyProgramElement.getCursor();
        SyntaxElement next;

        do {
            // First node can never be null as cursor is initialized with 'this'
            next = c.getCurrentNode();
            // Handle special cases so that hashCodeModThisProperty follows equalsModThisProperty
            if (next instanceof IdentPattern ip) {
                hashCode = 31 * hashCode + (ip.isMutable() ? 1 : 0);
                hashCode = 31 * hashCode + (ip.isReference() ? 1 : 0);
                absMap.add(((Identifier) ip.getChild(0)).name());
            } else if (next instanceof ProgramVariable || next instanceof Identifier) {
                Name name =
                    next instanceof ProgramVariable pv ? pv.name() : ((Identifier) next).name();
                hashCode = 31 * hashCode + absMap.getAbstractName(name);
            } else if (next.getChildCount() > 0) {
                hashCode = 31 * hashCode + next.getChildCount();
            } else {
                hashCode = 31 * hashCode + next.hashCode();
            }
            // walk to the next nodes in the tree
        } while (c.goToNext());

        return hashCode;
    }

    /*------------- Helper methods for special cases in equalsModThisProperty --------------*/
    /**
     * Handles the standard case of comparing two {@link SyntaxElement}s modulo renaming.
     *
     * @param se1 the first {@link SyntaxElement} to be compared
     * @param se2 the second {@link SyntaxElement} to be compared
     * @return {@code true} iff the two source elements are equal under the standard {@code equals}
     *         method
     */
    private boolean handleStandard(SyntaxElement se1, SyntaxElement se2) {
        return se1.equals(se2);
    }

    /**
     * Handles the special case of comparing a {@link } to a {@link SyntaxElement}.
     *
     * @param rnte the rusty program element with children to be compared
     * @param se the {@link SyntaxElement} to be compared
     * @return {@code true} iff {@code se} is of the same class and has the same number of children
     *         as {@code jnte}
     */
    private boolean handleRustyNonTerminalProgramElement(SyntaxElement rnte,
            SyntaxElement se) {
        /*
         * In the case of non-terminal RustyProgramElements, we must not traverse the children
         * recursively through the normal equals method. This is the case as we might have to
         * add some entries of children nodes to a NameAbstractionTable so that they can be
         * compared later on.
         */
        if (se == rnte) {
            return true;
        }
        if (se.getClass() != rnte.getClass()) {
            return false;
        }
        return rnte.getChildCount() == se.getChildCount();
    }

    /**
     * Handles the special case of comparing a {@link IdentPattern} to a
     * {@link SyntaxElement}.
     *
     * @param ip the {@link IdentPattern} to be compared
     * @param se the {@link SyntaxElement} to be compared
     * @param nat the {@link NameAbstractionTable} the variable of {@code vs} should be added to
     * @return {@code true} iff {@code se} is of the same class as {@code vs} and has the same
     *         number of children, dimensions and type
     */
    private boolean handleIdentPattern(IdentPattern ip, SyntaxElement se,
            NameAbstractionTable nat) {
        if (se == ip) {
            return true;
        }
        if (se.getClass() != ip.getClass()) {
            return false;
        }
        final IdentPattern other = (IdentPattern) se;
        if (ip.isMutable() != other.isMutable() || ip.isReference() != other.isReference()) {
            return false;
        }

        // Once Rust programs are parsed with the Rust Parser, this should be changed to not just
        // use the name of the Identifier
        Name ipName = ((Identifier) ip.getChild(0)).name();
        Name otherName = ((Identifier) other.getChild(0)).name();
        nat.add(ipName, otherName);
        return true;
    }

    /**
     * Handles the special case of comparing a {@link ProgramVariable} or an
     * {@link Identifier} to a {@link SyntaxElement}.
     *
     * @param se1 the first {@link SyntaxElement} which is either a {@link ProgramVariable} or an
     *        {@link Identifier}
     * @param se2 the second {@link SyntaxElement} to be compared
     * @param nat the {@link NameAbstractionTable} that should be used to check whether {@code se1}
     *        and {@code se2} have the same abstract name
     * @return {@code true} iff {@code se1} and {@code se2} have the same abstract name
     */
    private boolean handleProgramVariableOrIdentifier(SyntaxElement se1, SyntaxElement se2,
            NameAbstractionTable nat) {
        if (se1 == se2) {
            return true;
        }
        if (se1.getClass() != se2.getClass()) {
            return false;
        }

        Name name1, name2;
        if (se1 instanceof ProgramVariable pv) {
            name1 = pv.name();
            name2 = ((ProgramVariable) se2).name();
        } else {
            name1 = ((Identifier) se1).name();
            name2 = ((Identifier) se2).name();
        }

        return nat.sameAbstractName(name1, name2);
    }


    /* ---------- End of helper methods for special cases in equalsModThisProperty ---------- */

    /**
     * A helper class to map {@link Name}s to an abstract name.
     * <p>
     * As names are abstracted from in this property, we need to give named elements abstract names
     * for them to be used in the hash code. This approach is similar to
     * {@link NameAbstractionTable}, where we collect elements with names in the order they are
     * declared. Each element is associated with the number of previously added elements, which is
     * then used as the abstract name.
     */
    private static class NameAbstractionMap {
        private int nextAbstractName = 0;

        /**
         * The map that associates {@link Name}s with their abstract names.
         */
        private final Map<Name, Integer> map = new HashMap<>();

        /**
         * Adds a {@link Name} to the map.
         *
         * @param name the {@link Name} to be added
         */
        public void add(Name name) {
            map.put(name, nextAbstractName++);
        }

        /**
         * Returns the abstract name of a {@link Name} or {@code -1} if the element
         * is not in the map.
         * ee
         *
         * @param name the {@link Name} whose abstract name should be returned
         * @return the abstract name of the {@link Name} or {@code -1} if the element
         *         is
         *         not in the map
         */
        public int getAbstractName(Name name) {
            final Integer result = map.get(name);
            return result != null ? result : -1;
        }
    }
}
