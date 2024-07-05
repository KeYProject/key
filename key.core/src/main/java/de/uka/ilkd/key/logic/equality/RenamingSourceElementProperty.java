/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.SyntaxElementCursor;

/**
 * A property that can be used in
 * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])} for
 * {@link SourceElement}s.
 * <p>
 * The single instance of this property can be accessed through
 * {@link RenamingSourceElementProperty#RENAMING_SOURCE_ELEMENT_PROPERTY}.
 *
 * @author Tobias Reinhold
 */
public class RenamingSourceElementProperty implements Property<SourceElement> {
    /**
     * The single instance of this property.
     */
    public static final RenamingSourceElementProperty RENAMING_SOURCE_ELEMENT_PROPERTY =
        new RenamingSourceElementProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed
     * through {@link RenamingSourceElementProperty#RENAMING_SOURCE_ELEMENT_PROPERTY} and is used as
     * a parameter for
     * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])}.
     */
    private RenamingSourceElementProperty() {}

    /**
     * Checks if {@code se2} is a source element syntactically equal to {@code se1} modulo renaming.
     * <p>
     * When this method is supplied with a {@link NameAbstractionTable}, it will use this table to
     * compare the abstract names of the source elements. If no {@link NameAbstractionTable} is
     * supplied, a new one will be created.
     *
     * @param se1 the first element of the equality check
     * @param se2 the second element of the equality check
     * @param v can be a single {@link NameAbstractionTable} for this equality check
     * @return {@code true} iff {@code se2} is a source element syntactically equal to {@code se1}
     *         modulo renaming
     * @param <V> is supposed to be {@link NameAbstractionTable} for this equality check
     */
    @Override
    public <V> boolean equalsModThisProperty(SourceElement se1, SourceElement se2, V... v) {
        NameAbstractionTable nat;
        if (v.length > 0 && (v[0] instanceof NameAbstractionTable n)) {
            nat = n;
        } else {
            nat = new NameAbstractionTable();
        }

        SyntaxElementCursor c1 = se1.getCursor(), c2 = se2.getCursor();
        SyntaxElement next1, next2;
        boolean hasNext1, hasNext2; // Check at the end if both cursors have reached the end

        do {
            // First nodes can never be null as cursor is initialized with 'this'
            next1 = c1.getCurrentNode();
            next2 = c2.getCurrentNode();
            // Handle special cases of prior equalsModRenaming implementation
            if (next1 instanceof LabeledStatement ls) {
                if (!handleLabeledStatement(ls, next2, nat)) {
                    return false;
                }
            } else if (next1 instanceof VariableSpecification vs) {
                if (!handleVariableSpecification(vs, next2, nat)) {
                    return false;
                }
            } else if (next1 instanceof ProgramVariable || next1 instanceof ProgramElementName) {
                if (!handleProgramVariableOrElementName(next1, next2, nat)) {
                    return false;
                }
            } else if (next1 instanceof JavaNonTerminalProgramElement jnte) {
                if (!handleJavaNonTerminalProgramElements(jnte,
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

    @Override
    public int hashCodeModThisProperty(SourceElement sourceElement) {
        throw new UnsupportedOperationException(
            "Hashing of SourceElements modulo renaming not yet implemented!");
    }

    /* --------------------- Helper methods for special cases ---------------------- */
    /**
     * Handles the standard case of comparing two {@link SyntaxElement}s modulo renaming.
     *
     * @param se1 the first {@link SyntaxElement} to be compared
     * @param se2 the second {@link SyntaxElement} to be compared
     * @return {@code true} iff the two source elements are equal under the standard {@code equals}
     *         method
     */
    private boolean handleStandard(SyntaxElement se1, SyntaxElement se2) {
        /*
         * As the prior implementations of equalsModRenaming for SourceElements were mostly the same
         * as their normal equals methods, we decided to move equalsModRenaming completely into the
         * equals method and handle the special cases separately while walking through the tree that
         * is a SourceElement.
         */
        return se1.equals(se2);
    }

    /**
     * Handles the special case of comparing a {@link JavaNonTerminalProgramElement} to a
     * {@link SyntaxElement}.
     *
     * @param jnte the {@link JavaNonTerminalProgramElement} to be compared
     * @param se the {@link SyntaxElement} to be compared
     * @return {@code true} iff {@code se} is of the same class and has the same number of children
     *         as {@code jnte}
     */
    private boolean handleJavaNonTerminalProgramElements(JavaNonTerminalProgramElement jnte,
            SyntaxElement se) {
        /*
         * A JavaNonTerminalProgramElement is a special case of a SourceElement, as we must not
         * traverse the children recursively through the normal equals method. This is the case
         * as we might have to add some entries of children nodes to a NameAbstractionTable so
         * that they can be compared later on by the TreeWalker.
         */
        if (se == jnte) {
            return true;
        }
        if (se.getClass() != jnte.getClass()) {
            return false;
        }
        final JavaNonTerminalProgramElement other = (JavaNonTerminalProgramElement) se;
        return jnte.getChildCount() == other.getChildCount();
    }

    /**
     * Handles the special case of comparing a {@link LabeledStatement} to a {@link SyntaxElement}.
     *
     * @param ls the {@link LabeledStatement} to be compared
     * @param se the {@link SyntaxElement} to be compared
     * @param nat the {@link NameAbstractionTable} the label of {@code ls} should be added to
     * @return {@code true} iff {@code se} is also a {@link LabeledStatement} and has the same
     *         number of children as {@code ls}
     */
    private boolean handleLabeledStatement(LabeledStatement ls, SyntaxElement se,
            NameAbstractionTable nat) {
        /*
         * A LabeledStatement is a special case of a JavaNonTerminalProgramElement, as we must also
         * not traverse the children recursively but also additionally add the label to a NAT.
         */
        if (se == ls) {
            return true;
        }
        if (se.getClass() != ls.getClass()) {
            return false;
        }
        final LabeledStatement other = (LabeledStatement) se;
        if (ls.getChildCount() != other.getChildCount()) {
            return false;
        }
        nat.add(ls.getLabel(), ((LabeledStatement) se).getLabel());
        return true;
    }

    /**
     * Handles the special case of comparing a {@link VariableSpecification} to a
     * {@link SyntaxElement}.
     *
     * @param vs the {@link VariableSpecification} to be compared
     * @param se the {@link SyntaxElement} to be compared
     * @param nat the {@link NameAbstractionTable} the variable of {@code vs} should be added to
     * @return {@code true} iff {@code se} is of the same class as {@code vs} and has the same
     *         number of children, dimensions and type
     */
    private boolean handleVariableSpecification(VariableSpecification vs, SyntaxElement se,
            NameAbstractionTable nat) {
        /*
         * A VariableSpecification is a special case of a JavaNonTerminalProgramElement similar to
         * LabeledStatement, but we also need to check the dimensions and type of the
         * VariableSpecification.
         */
        if (se == vs) {
            return true;
        }
        if (se.getClass() != vs.getClass()) {
            return false;
        }
        final VariableSpecification other = (VariableSpecification) se;
        if (vs.getChildCount() != other.getChildCount()) {
            return false;
        }
        if (vs.getDimensions() != other.getDimensions()) {
            return false;
        }
        if (vs.getType() != null) {
            if (!vs.getType().equals(other.getType())) {
                return false;
            }
        } else {
            if (other.getType() != null) {
                return false;
            }
        }
        nat.add(vs.getProgramVariable(), other.getProgramVariable());
        return true;
    }

    /**
     * Handles the special case of comparing a {@link ProgramVariable} or a
     * {@link ProgramElementName} to a {@link SyntaxElement}.
     *
     * @param se1 the first {@link SyntaxElement} which is either a {@link ProgramVariable} or a
     *        {@link ProgramElementName}
     * @param se2 the second {@link SyntaxElement} to be compared
     * @param nat the {@link NameAbstractionTable} that should be used to check whether {@code se1}
     *        and {@code se2} have the same abstract name
     * @return {@code true} iff {@code se1} and {@code se2} have the same abstract name
     */
    private boolean handleProgramVariableOrElementName(SyntaxElement se1, SyntaxElement se2,
            NameAbstractionTable nat) {
        /*
         * A ProgramVariable or a ProgramElementName is a special case of a SourceElement and one
         * of the main reasons for equalsModRenaming. Equality here comes down to checking the
         * abstract name of the elements in a NAT.
         */
        if (se1.getClass() != se2.getClass()) {
            return false;
        }
        // We can cast here as se1 is either a ProgramVariable or a ProgramElementName
        // (this method is only called for these two classes in equalsModThisProperty)
        // and se2 is of the same class as se1
        return nat.sameAbstractName((SourceElement) se1, (SourceElement) se2);
    }


    /* ------------------ End of helper methods for special cases ------------------ */
}
