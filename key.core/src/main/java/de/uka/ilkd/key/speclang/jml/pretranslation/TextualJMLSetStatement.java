/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;

/**
 * A JML set statement in textual form.
 */
public final class TextualJMLSetStatement extends TextualJMLConstruct {

    private final JmlParser.Set_statementContext assignment;


    public TextualJMLSetStatement(ImmutableList<JMLModifier> mods,
            JmlParser.Set_statementContext assignment) {
        super(mods);
        assert assignment != null;
        this.assignment = assignment;
        setPosition(assignment);
    }


    public JmlParser.Set_statementContext getAssignment() {
        return assignment;
    }


    @Override
    public String toString() {
        return assignment.toString();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLSetStatement)) {
            return false;
        }
        TextualJMLSetStatement ss = (TextualJMLSetStatement) o;
        return mods.equals(ss.mods) && assignment.equals(ss.assignment);
    }


    @Override
    public int hashCode() {
        return mods.hashCode() + assignment.hashCode();
    }
}
