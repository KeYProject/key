/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.util.collection.ImmutableList;


/**
 * A JML initially clause declaration in textual form.
 *
 * @author Daniel Bruns
 */
public final class TextualJMLInitially extends TextualJMLConstruct {

    private final LabeledParserRuleContext inv;


    public TextualJMLInitially(ImmutableList<JMLModifier> mods, LabeledParserRuleContext inv) {
        super(mods);
        assert inv != null;
        this.inv = inv;
        setPosition(inv);
    }

    public LabeledParserRuleContext getInv() {
        return inv;
    }

    @Override
    public String toString() {
        return inv.first.getText();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLInitially ci)) {
            return false;
        }
        return mods.equals(ci.mods) && inv.equals(ci.inv);
    }


    @Override
    public int hashCode() {
        return mods.hashCode() + inv.hashCode();
    }
}
