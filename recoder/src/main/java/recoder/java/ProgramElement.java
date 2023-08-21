/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import recoder.ModelElement;
import recoder.java.expression.Literal;
import recoder.java.expression.literal.*;
import recoder.java.reference.*;
import recoder.list.generic.ASTList;
import recoder.util.Equality;
import recoder.util.HashCode;

/**
 * A part of the program syntax that carries semantics in the model.
 *
 * @author AL
 */

public interface ProgramElement extends SourceElement, ModelElement {

    /**
     * Structural hash code object for program elements.
     *
     * @see ProgramElement.TreeStructure#hashCode
     */

    HashCode STRUCTURAL_HASH_CODE = new TreeStructure();
    /**
     * Structural equality object for syntax trees.
     *
     * @see ProgramElement.TreeStructure#equals
     */

    Equality STRUCTURAL_EQUALITY = STRUCTURAL_HASH_CODE;

    /**
     * Yields the syntactical parent node.
     *
     * @return the parent node in the syntax tree.
     */
    NonTerminalProgramElement getASTParent();

    /**
     * Get comments.
     *
     * @return the comments.
     */
    ASTList<Comment> getComments();

    /**
     * Set comments.
     *
     * @param c a comment list.
     */
    void setComments(ASTList<Comment> list);

    /**
     * Provides hashcodes and structural equality checking for syntax trees. This class circumvents
     * a bug in the javadoc tool and should be an anonymous inner class instead.
     */

    class TreeStructure implements HashCode {

        /**
         * Structural hash code for program elements. The hash code calculated takes into acount the
         * type of the element, its name if it is a {@link recoder.java.NamedProgramElement}and the
         * number of its children. For reasons of efficiency, no further recursion is performed.
         *
         * @return the hash code.
         */

        public int hashCode(Object x) {
            if (x instanceof ProgramElement) {
                int res = getClass().hashCode();
                if (x instanceof NonTerminalProgramElement) {
                    if (x instanceof NamedProgramElement) {
                        String name = ((NamedProgramElement) x).getName();
                        if (name != null) {
                            // could be anonymous (class declaration!)
                            res ^= name.hashCode();
                        }
                    }
                    res += ((NonTerminalProgramElement) x).getChildCount();
                }
                return res;
            } else if (x == null) {
                return 0;
            } else {
                throw new IllegalArgumentException(
                    "Structural hashcodes are only defined for program elements");
            }
        }

        /**
         * Structural equality for syntax trees. To be considered equal, the types of the objects
         * must match, except for certain allowed combinations with
         * {@link recoder.java.reference.UncollatedReferenceQualifier}s.<BR>
         * In case of {@link recoder.java.Identifier}or {@link recoder.java.expression.Literal}s,
         * the textual representations are compared, while
         * {@link recoder.java.declaration.Modifier}are compared by type only. <BR>
         * {@link recoder.java.NonTerminalProgramElement}s are compared child-by-child in the given
         * order. Note that the corresponding iterator reports all children without separation. In
         * case that two children of the same type play different roles (e.g. return types of
         * methods and thrown exceptions if there was no need for a method name), this behavior must
         * be overriden. <BR>
         * The function does not compare comments or indentation information. Instead, the toSource
         * method can be used to perform a more stringent comparison.
         *
         * @param x the root of the first syntax tree.
         * @param y the root of the second syntax tree.
         * @return true, iff both roots have the same class and equal children (if any).
         */

        public boolean equals(Object x, Object y) {
            if (x == null || y == null) {
                return false;
            }
            if (x instanceof NonTerminalProgramElement) {
                if (x.getClass() != y.getClass()) {
                    if (x instanceof UncollatedReferenceQualifier) {
                        if (!(y instanceof ArrayLengthReference) && !(y instanceof PackageReference)
                                && !(y instanceof TypeReference)
                                && !(y instanceof VariableReference)) {
                            return false;
                        }
                    } else if (y instanceof UncollatedReferenceQualifier) {
                        if (!(x instanceof ArrayLengthReference) && !(x instanceof PackageReference)
                                && !(x instanceof TypeReference)
                                && !(x instanceof VariableReference)) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                NonTerminalProgramElement a = (NonTerminalProgramElement) x;
                NonTerminalProgramElement b = (NonTerminalProgramElement) y;
                int n = a.getChildCount();
                int m = b.getChildCount();
                if ((a instanceof ArrayLengthReference)
                        && (b instanceof UncollatedReferenceQualifier)) {
                    m -= 1;
                }
                if ((b instanceof ArrayLengthReference)
                        && (a instanceof UncollatedReferenceQualifier)) {
                    n -= 1;
                }
                if (n != m) {
                    return false;
                }
                for (int i = 0; i < n; i += 1) {
                    if (!equals(a.getChildAt(i), b.getChildAt(i))) {
                        return false;
                    }
                }
                return true;
            } else if (x instanceof TerminalProgramElement) {
                if (x.getClass() != y.getClass()) {
                    return false;
                }
                if (x instanceof Identifier) {
                    return ((Identifier) x).getText().equals(((Identifier) y).getText());
                }
                if (x instanceof Literal) {
                    if (x instanceof IntLiteral) {
                        return ((IntLiteral) x).getValue().equals(((IntLiteral) y).getValue());
                    }
                    if (x instanceof BooleanLiteral) {
                        return ((BooleanLiteral) x).getValue() == ((BooleanLiteral) y).getValue();
                    }
                    if (x instanceof StringLiteral) {
                        return ((StringLiteral) x).getValue()
                                .equals(((StringLiteral) y).getValue());
                    }
                    if (x instanceof NullLiteral) {
                        return true;
                    }
                    if (x instanceof CharLiteral) {
                        return ((CharLiteral) x).getValue().equals(((CharLiteral) y).getValue());
                    }
                    if (x instanceof DoubleLiteral) {
                        return ((DoubleLiteral) x).getValue()
                                .equals(((DoubleLiteral) y).getValue());
                    }
                    if (x instanceof LongLiteral) {
                        return ((LongLiteral) x).getValue().equals(((LongLiteral) y).getValue());
                    }
                    if (x instanceof FloatLiteral) {
                        return ((FloatLiteral) x).getValue().equals(((FloatLiteral) y).getValue());
                        // modifiers and EmptyStatement are covered by the class
                        // test
                    }
                }
                return true;
            } else {
                throw new IllegalArgumentException(
                    "Structural equality is only defined for program elements");
            }
        }
    }
}
