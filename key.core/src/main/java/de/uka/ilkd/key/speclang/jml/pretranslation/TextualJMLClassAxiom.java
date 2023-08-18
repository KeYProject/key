/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * A JML axiom declaration in textual form. According to Sect. 8 of the JML reference manual, axioms
 * may not have any modifiers.
 */
public final class TextualJMLClassAxiom extends TextualJMLConstruct {
    private final LabeledParserRuleContext inv;

    /**
     * new textual representation.
     *
     * @param mods modifiers (are currently ignored)
     * @param inv the expression in this clause
     */
    public TextualJMLClassAxiom(ImmutableList<JMLModifier> mods, LabeledParserRuleContext inv) {
        super(ImmutableSLList.nil()); // no modifiers allowed in axiom clause (see
                                      // Sect. 8 of reference manual)
        assert inv != null;
        this.inv = inv;
        setPosition(inv);
    }

    public TextualJMLClassAxiom(ImmutableList<JMLModifier> mods, LabeledParserRuleContext inv,
            String name) {
        this(mods, inv);
        this.name = name;
    }


    public LabeledParserRuleContext getAxiom() {
        return inv;
    }


    @Override
    public String toString() {
        return inv.toString();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLClassAxiom)) {
            return false;
        }
        TextualJMLClassAxiom ci = (TextualJMLClassAxiom) o;
        return mods.equals(ci.mods) && inv.equals(ci.inv);
    }


    @Override
    public int hashCode() {
        return mods.hashCode() + inv.hashCode();
    }

    public String getName() {
        return name;
    }
}
