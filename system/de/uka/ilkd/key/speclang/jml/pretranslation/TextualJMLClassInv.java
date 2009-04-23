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
import de.uka.ilkd.key.speclang.PositionedString;


public class TextualJMLClassInv extends TextualJMLConstruct {
    
    private final PositionedString inv;
    
    
    public TextualJMLClassInv(ListOfString mods, PositionedString inv) {
        super(mods);
        assert inv != null;
        this.inv = inv;
    }
    
    
    public PositionedString getInv() {
        return inv;
    }
    
    
    public String toString() {
        return inv.toString();
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLClassInv)) {
            return false;
        }
        TextualJMLClassInv ci = (TextualJMLClassInv) o;
        return mods.equals(ci.mods) && inv.equals(ci.inv);
    }
    
    
    public int hashCode() {
        return mods.hashCode() + inv.hashCode();
    }
}
