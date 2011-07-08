// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.collection.ImmutableList;


/**
 * Objects of this type represent the various JML specification constructs
 * in textual, unprocessed form.
 */
public abstract class TextualJMLConstruct {
    
    protected final ImmutableList<String> mods;
    
    /** A user-provided identifier to keep an overview over large specification collections */
    protected String name;
    
    
    public TextualJMLConstruct(ImmutableList<String> mods) {
        assert mods != null;
        this.mods = mods;
    }
    
    public TextualJMLConstruct(ImmutableList<String> mods, String name){
        this(mods);
        this.name = name;
    }
    
    
    public final ImmutableList<String> getMods() {
        return mods;
    }
}
