/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.ccatch;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A "\Break label" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
@NullMarked
public class CcatchBreakLabelParameterDeclaration extends CcatchNonstandardParameterDeclaration {

    private final @Nullable Label label;

    // The label is optional (a "\Break label" clause without a label is constructed from an
    // ExtList that contains no Label), so the field and getter are honestly @Nullable.
    public CcatchBreakLabelParameterDeclaration(ExtList children) {
        label = children.get(Label.class);
    }

    public CcatchBreakLabelParameterDeclaration(PositionInfo pi, List<Comment> c, Label label) {
        super(pi, c);
        this.label = label;
    }

    @Override
    public int getChildCount() {
        return (label != null) ? 1 : 0;
    }

    public @Nullable Label getLabel() {
        return label;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        final Label l = label;
        if (l != null) {
            if (index == 0) {
                return l;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCcatchBreakLabelParameterDeclaration(this);
    }

}
