/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.Objects;

import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;


/**
 * A JML merge point declaration in textual form.
 * <p>
 * TODO: Adapt this to the specific needs of merge point declarations.
 *
 * @author Dominic Scheurer
 */
@NullMarked
public final class TextualJMLMergePointDecl extends TextualJMLConstruct {

    private final JmlParser.Merge_point_statementContext mergeProc;

    public TextualJMLMergePointDecl(ImmutableList<JMLModifier> mods,
            JmlParser.Merge_point_statementContext mergeProc) {
        super(mods);
        this.mergeProc = mergeProc;
        setPosition(mergeProc);
    }

    public JmlParser.Merge_point_statementContext getMergeProc() {
        return mergeProc;
    }

    @Override
    public String toString() {
        return "TextualJMLMergePointDecl{" + "mergeProc=" + mergeProc.getText() + ", mods=" + mods
            + ", name='" + name + '\'' + '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof TextualJMLMergePointDecl that)) {
            return false;
        }
        return getMergeProc().equals(that.getMergeProc());
    }

    @Override
    public int hashCode() {
        return Objects.hash(getMergeProc());
    }
}
