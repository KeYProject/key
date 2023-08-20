/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.util.collection.ImmutableList;

/**
 * A JML represents clause in textual form.
 */
public final class TextualJMLRepresents extends TextualJMLConstruct {

    private final LabeledParserRuleContext represents;


    public TextualJMLRepresents(ImmutableList<JMLModifier> mods,
            LabeledParserRuleContext represents) {
        super(mods);
        assert represents != null;
        this.represents = represents;
        setPosition(represents);
    }

    public TextualJMLRepresents(ImmutableList<JMLModifier> mods,
            LabeledParserRuleContext represents, String name) {
        this(mods, represents);
        this.name = name;
    }

    public LabeledParserRuleContext getRepresents() {
        return represents;
    }

    @Override
    public String toString() {
        return represents.toString();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLRepresents)) {
            return false;
        }
        TextualJMLRepresents r = (TextualJMLRepresents) o;
        return mods.equals(r.mods) && represents.equals(r.represents);
    }


    @Override
    public int hashCode() {
        return mods.hashCode() + represents.hashCode();
    }

    public String getName() {
        return name;
    }
}
