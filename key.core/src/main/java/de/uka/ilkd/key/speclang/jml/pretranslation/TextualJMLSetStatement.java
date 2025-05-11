/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/**
 * A JML set statement in textual form.
 */
public final class TextualJMLSetStatement extends TextualJMLConstruct {

    private final JmlParser.@NonNull Set_statementContext assignment;


    public TextualJMLSetStatement(@NonNull ImmutableList<JMLModifier> modifiers,
            JmlParser.@NonNull Set_statementContext assignment) {
        super(modifiers);
        assert assignment != null;
        this.assignment = assignment;
        setPosition(assignment);
    }


    public JmlParser.@NonNull Set_statementContext getAssignment() {
        return assignment;
    }


    @Override
    public String toString() {
        return assignment.toString();
    }


    @Override
    public boolean equals(@org.jspecify.annotations.Nullable Object o) {
        if (!(o instanceof TextualJMLSetStatement ss)) {
            return false;
        }
        return modifiers.equals(ss.modifiers) && assignment.equals(ss.assignment);
    }


    @Override
    public int hashCode() {
        return modifiers.hashCode() + assignment.hashCode();
    }
}
