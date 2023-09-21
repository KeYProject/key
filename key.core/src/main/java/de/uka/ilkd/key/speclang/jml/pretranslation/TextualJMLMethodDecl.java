/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.Objects;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.recoderext.JMLTransformer;
import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.ParserRuleContext;

/**
 * A JML model method declaration in textual form.
 */
public final class TextualJMLMethodDecl extends TextualJMLConstruct {
    private final JmlParser.Method_declarationContext methodDefinition;


    public TextualJMLMethodDecl(ImmutableList<JMLModifier> mods,
            JmlParser.Method_declarationContext methodDefinition) {
        super(mods);
        this.methodDefinition = methodDefinition;
        setPosition(methodDefinition);
    }

    public String getParsableDeclaration() {
        String m = mods.stream().map(it -> {
            if (JMLTransformer.javaMods.contains(it)) {
                return it.toString();
            } else {
                return StringUtil.repeat(" ", it.toString().length());
            }
        }).collect(Collectors.joining(" "));

        String paramsString = methodDefinition.param_list().param_decl().stream()
                .map(it -> it.typespec().getText() + " " + it.p.getText()
                    + StringUtil.repeat("[]", it.LBRACKET().size()))
                .collect(Collectors.joining(","));
        return String.format("%s %s %s (%s);", m, methodDefinition.typespec().getText(),
            getMethodName(), paramsString);
    }

    public JmlParser.Method_declarationContext getDecl() {
        return methodDefinition;
    }

    public String getMethodName() {
        return methodDefinition.IDENT().getText();
    }

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

    public int getStateCount() {
        if (mods.contains(JMLModifier.TWO_STATE)) {
            return 2;
        }
        if (mods.contains(JMLModifier.NO_STATE)) {
            return 0;
        }
        return 1;
    }

}
