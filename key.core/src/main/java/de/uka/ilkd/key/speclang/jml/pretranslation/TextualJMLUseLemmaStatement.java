/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.List;

import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;

/**
 * A JML "use_lemma" statement in textual form.
 */
public final class TextualJMLUseLemmaStatement extends TextualJMLConstruct {

    private final JmlParser.Use_lemma_statementContext statement;


    public TextualJMLUseLemmaStatement(ImmutableList<JMLModifier> modifiers,
            JmlParser.Use_lemma_statementContext statement) {
        super(modifiers);
        assert statement != null;
        this.statement = statement;
    }

    public boolean isSuitableExpression() {
        JmlParser.PostfixexprContext postfix = statement.postfixexpr();
        JmlParser.PrimaryexprContext prim = postfix.primaryexpr();
        List<JmlParser.PrimarysuffixContext> primarysuffix = postfix.primarysuffix();
        if (primarysuffix.size() != 1) {
            return false;
        }
        JmlParser.PrimarysuffixContext args = primarysuffix.get(0);
        if (!(args instanceof JmlParser.PrimarySuffixCallContext)) {
            return false;
        }
        return true;
    }

    public JmlParser.PostfixexprContext getExpression() {
        return statement.postfixexpr();
    }

    @Override
    public String toString() {
        return statement.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLUseLemmaStatement ss)) {
            return false;
        }
        return modifiers.equals(ss.modifiers) && statement.equals(ss.statement);
    }

    @Override
    public int hashCode() {
        return modifiers.hashCode() + statement.hashCode();
    }
}
