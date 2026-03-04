/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import org.key_project.util.collection.ImmutableList;


/**
 * A list of {@link JMLModifier}s that apply to some class-level element (e.g., field declaration, method declaration).
 *
 * @author lanzinger
 */
public final class TextualJMLModifierList extends TextualJMLConstruct {

    public TextualJMLModifierList(ImmutableList<JMLModifier> modifiers) {
        super(modifiers);
    }

    @Override
    public String toString() {
        return modifiers.stream().map(JMLModifier::toString).reduce("", (s0, s1) -> s0 + " " + s1);
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLModifierList ci)) {
            return false;
        }
        return modifiers.equals(ci.modifiers);
    }


    @Override
    public int hashCode() {
        return modifiers.hashCode();
    }
}
