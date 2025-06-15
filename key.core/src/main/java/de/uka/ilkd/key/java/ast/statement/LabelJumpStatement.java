/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;


import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.reference.NameReference;
import de.uka.ilkd.key.logic.ProgramElementName;

import org.key_project.util.ExtList;

/**
 * Label jump statement.
 */

public abstract class LabelJumpStatement extends JumpStatement implements NameReference {

    /**
     * Name.
     */

    protected final Label name;

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

    public LabelJumpStatement(PositionInfo pi, List<Comment> c, Label name) {
        super(pi, c);
        this.name = name;
    }


    /**
     * Get name.
     *
     * @return the string.
     */
    public final String getName() {
        return (name == null) ? null : name.toString();
    }

    /**
     * Get Label.
     *
     * @return the Label label
     */

    public Label getLabel() {
        return name;
    }


    /**
     * Get identifier.
     *
     * @return the identifier.
     */
    public ProgramElementName getProgramElementName() {
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
