/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.Objects;

import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.ParserRuleContext;

/**
 * A JML lemma declaration in textual form.
 *
 * This is a special case of a textual JML method declaration.
 */
public final class TextualJMLLemmaDecl extends TextualJMLMethodOrLemmaDecl {
    private final JmlParser.Lemma_declarationContext lemmaDefinition;


    public TextualJMLLemmaDecl(ImmutableList<JMLModifier> modifiers,
            JmlParser.Lemma_declarationContext lemmaDefinition) {
        super(modifiers.append(JMLModifier.MODEL));
        this.lemmaDefinition = lemmaDefinition;
        setPosition(lemmaDefinition);
    }

    public String getMethodName() {
        return lemmaDefinition.IDENT().getText();
    }

    public ParserRuleContext getMethodDefinition() {
        return lemmaDefinition;
    }

    @Override
    public String toString() {
        return lemmaDefinition.getText();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        TextualJMLLemmaDecl that = (TextualJMLLemmaDecl) o;
        return Objects.equals(lemmaDefinition, that.lemmaDefinition);
    }

    @Override
    public int hashCode() {
        return Objects.hash(lemmaDefinition);
    }

    public int getStateCount() {
        if (modifiers.contains(JMLModifier.TWO_STATE)) {
            return 2;
        }
        if (modifiers.contains(JMLModifier.NO_STATE)) {
            return 0;
        }
        return 1;
    }

    @Override
    protected JmlParser.Param_listContext getParamListContext() {
        return lemmaDefinition.param_list();
    }

    @Override
    protected String getTypespecText() {
        return "boolean";
    }
}
