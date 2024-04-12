/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.visitor.JavaASTTreeWalker;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A property that can be used in
 * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])} for
 * {@link SourceElement}s.
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
     *
     * @param se1 the first element of the equality check
     * @param se2 the second element of the equality check
     * @param v the additional arguments needed for the equality check
     * @return {@code true} iff {@code se2} is a source element syntactically equal to {@code se1}
     *         modulo renaming
     * @param <V> the type of the additional parameters needed for the comparison
     */
    @Override
    public <V> boolean equalsModThisProperty(SourceElement se1, SourceElement se2, V... v) {
        // For this equality check, v must be a single NameAbstractionTable
        if (v.length != 1 || !(v[0] instanceof NameAbstractionTable)) {
            throw new IllegalArgumentException(
                "Expected a single NameAbstractionTable as argument.");
        }
        NameAbstractionTable nat = (NameAbstractionTable) v[0];

        JavaASTTreeWalker tw1 = new JavaASTTreeWalker(se1);
        JavaASTTreeWalker tw2 = new JavaASTTreeWalker(se2);

        SourceElement next1 = tw1.getCurrentNode();
        SourceElement next2 = tw2.getCurrentNode();

        while (next1 != null && next2 != null) {
            // Handle special cases of prior equalsModRenaming implementation
            if (next1 instanceof LabeledStatement) {
                if (!handleLabeledStatement((LabeledStatement) next1, next2, nat)) {
                    return false;
                }
            } else if (next1 instanceof VariableSpecification) {
                if (!handleVariableSpecification((VariableSpecification) next1, next2, nat)) {
                    return false;
                }
            } else if (next1 instanceof ProgramVariable || next1 instanceof ProgramElementName) {
                if (!handleProgramVariableOrElementName(next1, next2, nat)) {
                    return false;
                }
            } else if (next1 instanceof JavaNonTerminalProgramElement) {
                if (!handleJavaNonTerminalProgramElements((JavaNonTerminalProgramElement) next1,
                    next2)) {
                    return false;
                }
            } else {
                if (!handleStandard(next1, next2)) {
                    return false;
                }
            }

            // walk to the next nodes in the tree
            next1 = tw1.nextNode();
            next2 = tw2.nextNode();
        }

        return next1 == null && next2 == null;
    }

    @Override
    public int hashCodeModThisProperty(SourceElement sourceElement) {
        throw new UnsupportedOperationException(
            "Hashing of SourceElements modulo renaming not yet implemented!");
    }

    /* --------------------- Helper methods for special cases ---------------------- */
    /**
     * Handles the standard case of comparing two {@link SourceElement}s modulo renaming.
     *
     * @param se1 the first {@link SourceElement} to be compared
     * @param se2 the second {@link SourceElement} to be compared
     * @return {@code true} iff the two source elements are equal under the standard {@code equals}
     *         method
     */
    private boolean handleStandard(SourceElement se1, SourceElement se2) {
        /*
         * As the prior implementations of equalsModRenaming for SourceElements were mostly the same
         * as the normal equals method, we decided to move equalsModRenaming completely into the
         * equals method and handle the special cases separately while walking through the tree that
         * is a SourceElement.
         */
        return se1.equals(se2);
    }

    /**
     * Handles the special case of comparing a {@link JavaNonTerminalProgramElement} to a
     * {@link SourceElement}.
     *
     * @param jnte the {@link JavaNonTerminalProgramElement} to be compared
     * @param se the {@link SourceElement} to be compared
     * @return {@code true} iff {@code se} is of the same class and has the same number of children
     *         as {@code jnte}
     */
    private boolean handleJavaNonTerminalProgramElements(JavaNonTerminalProgramElement jnte,
            SourceElement se) {
        /*
         * A JavaNonTerminalProgramElement is a special case of a SourceElement, as we must not
         * traverse the children recursively. This is the case as we might have to add some entries
         * of children nodes to a NameAbstractionTable so that they can be compared later on by the
         * TreeWalker.
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
     * Handles the special case of comparing a {@link LabeledStatement} to a {@link SourceElement}.
     *
     * @param ls the {@link LabeledStatement} to be compared
     * @param se the {@link SourceElement} to be compared
     * @param nat the {@link NameAbstractionTable} the label of {@code ls} should be added to
     * @return {@code true} iff {@code se} is also a {@link LabeledStatement} and has the same
     *         number of children as {@code ls}
     */
    private boolean handleLabeledStatement(LabeledStatement ls, SourceElement se,
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
     * {@link SourceElement}.
     *
     * @param vs the {@link VariableSpecification} to be compared
     * @param se the {@link SourceElement} to be compared
     * @param nat the {@link NameAbstractionTable} the variable of {@code vs} should be added to
     * @return {@code true} iff {@code se} is of the same class as {@code vs} and has the same
     *         number of children, dimensions and type
     */
    private boolean handleVariableSpecification(VariableSpecification vs, SourceElement se,
            NameAbstractionTable nat) {
        /*
         * A VariableSpecification is a special case of a JavaNonTerminalProgramElement similar to
         * LabeledStatement, but we also need to check the dimensions and type of the
         * VariableSpecification.
         */
        if (se == vs) {
            return true;
        }
        // TODO: Checking for exact class might be too strict as the original implementation was
        // only using instanceof
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
     * {@link ProgramElementName} to a {@link SourceElement}.
     *
     * @param se1 the first {@link SourceElement} which is either a {@link ProgramVariable} or a
     *        {@link ProgramElementName}
     * @param se2 the second {@link SourceElement} to be compared
     * @param nat the {@link NameAbstractionTable} that should be used to check whether {@code se1}
     *        and {@code se2} have the same abstract name
     * @return {@code true} iff {@code se1} and {@code se2} have the same abstract name
     */
    private boolean handleProgramVariableOrElementName(SourceElement se1, SourceElement se2,
            NameAbstractionTable nat) {
        // TODO: Checking for exact class might be too strict as the original implementation was
        // only using instanceof or no check at all.
        if (se1.getClass() != se2.getClass()) {
            return false;
        }
        return nat.sameAbstractName(se1, se2);
    }


    /* ------------------ End of helper methods for special cases ------------------ */
}
