/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;


import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.reference.NameReference;
import de.uka.ilkd.key.logic.ProgramElementName;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Label jump statement.
 */

@NullMarked
public abstract class LabelJumpStatement extends JumpStatement implements NameReference {

    /**
     * Name.
     */

    protected final @Nullable Label name;

    /**
     * Label jump statement.
     */

    protected LabelJumpStatement() {
        name = null;
    }

    /**
     * Label jump statement.
     *
     * @param label
     *        the Label of this jump statement
     */

    protected LabelJumpStatement(Label label) {
        super();
        name = label;

    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children
     *        the children of this AST element as KeY classes.
     */
    protected LabelJumpStatement(ExtList children) {
        super(children);
        name = children.get(Label.class);
    }

    public LabelJumpStatement(PositionInfo pi, List<Comment> c, @Nullable Label name) {
        super(pi, c);
        this.name = name;
    }


    /**
     * Get name.
     *
     * @return the string.
     */
    // getName() returns null for unlabeled jumps (break;/continue;), which conflicts with the
    // @NonNull contract of NamedModelElement.getName(); the super-interface cannot be widened
    // without ripple (LabeledStatement and MethodDeclaration override it as well), so the
    // override-mismatch check is scoped here.
    @SuppressWarnings("NullAway")
    public final @Nullable String getName() {
        return (name == null) ? null : name.toString();
    }

    /**
     * Get Label.
     *
     * @return the Label label
     */

    public @Nullable Label getLabel() {
        return name;
    }


    /**
     * Get identifier.
     *
     * @return the identifier.
     */
    // returns null for labels that are not ProgramElementNames (and for unlabeled jumps), which
    // conflicts with the @NonNull contract of NamedProgramElement.getProgramElementName(); the
    // super-interface cannot be widened without ripple, so the check is scoped here.
    @SuppressWarnings("NullAway")
    public @Nullable ProgramElementName getProgramElementName() {
        if ((name instanceof ProgramElementName) || (name == null)) {
            return (ProgramElementName) name;
        }
        return null;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        return (name != null) ? 1 : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException
     *         if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (name != null) {
            if (index == 0) {
                return name;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }


}
