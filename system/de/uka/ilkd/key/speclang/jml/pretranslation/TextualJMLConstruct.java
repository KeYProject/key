// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.collection.ListOfString;


/**
 * Objects of this type represent the various JML specification constructs
 * in textual, unprocessed form.
 */
public abstract class TextualJMLConstruct {
    
    protected final ListOfString mods;
    
    
    public TextualJMLConstruct(ListOfString mods) {
        assert mods != null;
        this.mods = mods;
    }
    
    
    public ListOfString getMods() {
        return mods;
    }
}
