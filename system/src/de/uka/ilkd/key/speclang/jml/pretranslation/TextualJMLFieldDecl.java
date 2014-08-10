// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.speclang.PositionedString;

/**
 * A JML field declaration (ghost or model) in textual form.
 */
public final class TextualJMLFieldDecl extends TextualJMLConstruct {
    
    private final PositionedString decl;
    
    
    public TextualJMLFieldDecl(ImmutableList<String> mods, PositionedString decl) {
        super(mods);
        assert decl != null;
        this.decl = decl;
        setPosition(decl);
    }
    
    
    public PositionedString getDecl() {
        return decl;
    }
    
    
    @Override
    public String toString() {
        return decl.toString();
    }
    
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLFieldDecl)) {
            return false;
        }
        TextualJMLFieldDecl fd = (TextualJMLFieldDecl) o;
        return mods.equals(fd.mods) && decl.equals(fd.decl);
    }
    
    
    @Override
    public int hashCode() {
        return mods.hashCode() + decl.hashCode();
    }
}