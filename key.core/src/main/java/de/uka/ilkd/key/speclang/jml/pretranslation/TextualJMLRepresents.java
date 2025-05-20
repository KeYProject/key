/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/**
 * A JML represents clause in textual form.
 */
public final class TextualJMLRepresents extends TextualJMLConstruct {

    private final @NonNull LabeledParserRuleContext represents;


    public TextualJMLRepresents(@NonNull ImmutableList<JMLModifier> modifiers,
            @NonNull LabeledParserRuleContext represents) {
        super(modifiers);
        assert represents != null;
        this.represents = represents;
        setPosition(represents);
    }

    public TextualJMLRepresents(@NonNull ImmutableList<JMLModifier> modifiers,
            @NonNull LabeledParserRuleContext represents, String name) {
        this(modifiers, represents);
        this.name = name;
    }

    public @NonNull LabeledParserRuleContext getRepresents() {
        return represents;
    }

    @Override
    public String toString() {
        return represents.toString();
    }


    @Override
    public boolean equals(@org.jspecify.annotations.Nullable Object o) {
        if (!(o instanceof TextualJMLRepresents r)) {
            return false;
        }
        return modifiers.equals(r.modifiers) && represents.equals(r.represents);
    }


    @Override
    public int hashCode() {
        return modifiers.hashCode() + represents.hashCode();
    }

    public String getName() {
        return name;
    }
}
