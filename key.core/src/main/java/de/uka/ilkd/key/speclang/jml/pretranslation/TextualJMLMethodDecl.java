/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.Objects;

import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.ParserRuleContext;

/**
 * A JML model method declaration in textual form.
 */
public final class TextualJMLMethodDecl extends TextualJMLMethodOrLemmaDecl {
    private final JmlParser.Method_declarationContext methodDefinition;

    public TextualJMLMethodDecl(ImmutableList<JMLModifier> modifiers,
            JmlParser.Method_declarationContext methodDefinition) {
        super(modifiers);
        this.methodDefinition = methodDefinition;
        setPosition(methodDefinition);
    }

    // public JmlParser.Method_declarationContext getDecl() {
    // return methodDefinition;
    // }

    @Override
    public String getMethodName() {
        return methodDefinition.IDENT().getText();
    }

    @Override
    public ParserRuleContext getMethodDefinition() {
        return methodDefinition;
    }

    @Override
    public String toString() {
        return methodDefinition.getText();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        TextualJMLMethodDecl that = (TextualJMLMethodDecl) o;
        return Objects.equals(methodDefinition, that.methodDefinition);
    }

    @Override
    public int hashCode() {
        return Objects.hash(methodDefinition);
    }

    @Override
    protected JmlParser.Param_listContext getParamListContext() {
        return methodDefinition.param_list();
    }

    @Override
    protected String getTypespecText() {
        return methodDefinition.typespec().getText();
    }
}
