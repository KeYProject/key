/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A JML represents clause in textual form.
 */
@NullMarked
public final class TextualJMLRepresents extends TextualJMLConstruct {

    private final LabeledParserRuleContext represents;


    public TextualJMLRepresents(ImmutableList<JMLModifier> modifiers,
            LabeledParserRuleContext represents) {
        super(modifiers);
        assert represents != null;
        this.represents = represents;
        setPosition(represents);
    }

    public TextualJMLRepresents(ImmutableList<JMLModifier> modifiers,
            LabeledParserRuleContext represents, String name) {
        this(modifiers, represents);
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
    public boolean equals(@Nullable Object o) {
        if (!(o instanceof TextualJMLRepresents r)) {
            return false;
        }
        return modifiers.equals(r.modifiers) && represents.equals(r.represents);
    }


    @Override
    public int hashCode() {
        return modifiers.hashCode() + represents.hashCode();
    }

    public @Nullable String getName() {
        return name;
    }
}
