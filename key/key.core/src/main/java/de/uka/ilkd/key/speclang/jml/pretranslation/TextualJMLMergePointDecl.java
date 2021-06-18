// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.JmlParser;
import javax.annotation.Nonnull;
import org.key_project.util.collection.ImmutableList;

import java.util.Objects;

/**
 * A JML merge point declaration in textual form.
 * 
 * TODO: Adapt this to the specific needs of merge point declarations.
 *
 * @author Dominic Scheurer
 */
public final class TextualJMLMergePointDecl extends TextualJMLConstruct {
    private final @Nonnull JmlParser.Merge_point_statementContext mergeProc;

    public TextualJMLMergePointDecl(@Nonnull ImmutableList<String> mods,
                                    @Nonnull JmlParser.Merge_point_statementContext mergeProc) {
        super(mods);
        this.mergeProc = mergeProc;
        setPosition(mergeProc);
    }

    public @Nonnull JmlParser.Merge_point_statementContext getMergeProc() {
        return mergeProc;
    }

    @Override
    public String toString() {
        return "TextualJMLMergePointDecl{" +
                "mergeProc=" + mergeProc.getText() +
                ", mods=" + mods +
                ", name='" + name + '\'' +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof TextualJMLMergePointDecl)) return false;
        TextualJMLMergePointDecl that = (TextualJMLMergePointDecl) o;
        return getMergeProc().equals(that.getMergeProc());
    }

    @Override
    public int hashCode() {
        return Objects.hash(getMergeProc());
    }
}