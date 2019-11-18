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

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.speclang.PositionedString;

/**
 * A JML merge point declaration in textual form.
 * 
 * TODO: Adapt this to the specific needs of merge point declarations.
 *
 * @author Dominic Scheurer
 */
public final class TextualJMLMergePointDecl extends TextualJMLConstruct {

    private final PositionedString mergeProc;
    private final PositionedString mergeParams;

    public TextualJMLMergePointDecl(ImmutableList<String> mods) {
        super(mods);
        mergeProc = null;
        mergeParams = null;
    }

    public TextualJMLMergePointDecl(ImmutableList<String> mods,
            PositionedString mergeProc) {
        super(mods);
        assert mergeProc != null;
        this.mergeProc = mergeProc;
        mergeParams = null;
        setPosition(mergeProc);
    }

    public TextualJMLMergePointDecl(ImmutableList<String> mods,
            PositionedString mergeProc, PositionedString mergeParams) {
        super(mods);
        assert mergeProc != null;
        assert mergeParams != null;
        this.mergeProc = mergeProc;
        this.mergeParams = mergeParams;
        setPosition(mergeProc);
    }


    public PositionedString getMergeParams() {
        return mergeParams;
    }

    public PositionedString getMergeProc() {
        return mergeProc;
    }

    @Override
    public String toString() {
        return mergeProc.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLMergePointDecl)) {
            return false;
        }
        TextualJMLMergePointDecl fd = (TextualJMLMergePointDecl) o;
        return mods.equals(fd.mods) && mergeProc.equals(fd.mergeProc);
    }

    @Override
    public int hashCode() {
        return mods.hashCode() + mergeProc.hashCode();
    }
}