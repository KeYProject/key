/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.stream.Collectors;

import de.uka.ilkd.key.java.transformations.pipeline.JMLTransformer;
import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.ParserRuleContext;

public abstract class TextualJMLMethodOrLemmaDecl extends TextualJMLConstruct {

    public TextualJMLMethodOrLemmaDecl(ImmutableList<JMLModifier> specModifiers) {
        super(specModifiers);
    }

    public String getParsableDeclaration() {
        String m = modifiers.stream().map(it -> {
            if (JMLTransformer.JAVA_MODS.contains(it)) {
                return it.toString();
            } else {
                JMLModifier jmlModifier = JMLModifier.valueOf(it.name());
                if (jmlModifier == JMLModifier.NON_NULL || jmlModifier == JMLModifier.NULLABLE) {
                    return "/*@ " + jmlModifier + " @*/";
                } else {
                    return StringUtil.repeat(" ", it.toString().length());
                }
            }
        }).collect(Collectors.joining(" "));

        String paramsString = getParamListContext().param_decl().stream()
                .map(it -> (it.NULLABLE() != null ? "/*@ nullable @*/"
                        : it.NON_NULL() != null ? "/*@ non_null @*/" : "")
                    + " " + it.typespec().getText() + " " + it.p.getText()
                    + StringUtil.repeat("[]", it.LBRACKET().size()))
                .collect(Collectors.joining(","));
        return String.format("%s %s %s (%s);", m, getTypespecText(),
            getMethodName(), paramsString);
    }

    protected abstract JmlParser.Param_listContext getParamListContext();

    protected abstract String getTypespecText();

    public abstract String getMethodName();

    public abstract ParserRuleContext getMethodDefinition();

    public int getStateCount() {
        if (modifiers.contains(JMLModifier.TWO_STATE)) {
            return 2;
        }
        if (modifiers.contains(JMLModifier.NO_STATE)) {
            return 0;
        }
        return 1;
    }
}
