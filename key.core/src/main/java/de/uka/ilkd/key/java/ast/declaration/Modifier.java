/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import java.util.List;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.SyntaxElement;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 *
 *
 */
@NullMarked
public class Modifier extends JavaProgramElement {
    public static Modifier[] createModifierList(ModifierKind... modifierKind) {
        Modifier[] modifiers = new Modifier[modifierKind.length];
        for (int i = 0; i < modifierKind.length; i++) {
            modifiers[i] = new Modifier(modifierKind[i]);
        }
        return modifiers;
    }

    public ModifierKind getKind() {
        return keyword;
    }

    private final ModifierKind keyword;

    public Modifier(ModifierKind keyword) {
        this.keyword = keyword;
    }

    public Modifier(PositionInfo pi, List<Comment> c, ModifierKind keyword) {
        super(pi, c);
        this.keyword = keyword;
    }

    public String getText() {
        return keyword.asString();
    }

    public void visit(Visitor v) {
        v.performActionOnModifier(this);
    }


    @Override
    public @Nullable MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        if (src instanceof Modifier other) {
            if (this.keyword.equals(other.getKind())) {
                return super.match(source, matchCond);
            }
        }
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException(getClass() + " " + this + " has no children");
    }

    @Override
    public final boolean equals(Object o) {
        if (!(o instanceof Modifier modifier))
            return false;
        if (!super.equals(o))
            return false;

        return keyword.equals(modifier.keyword);
    }

    @Override
    public int computeHashCode() {
        return 31 * keyword.hashCode();
    }
}
