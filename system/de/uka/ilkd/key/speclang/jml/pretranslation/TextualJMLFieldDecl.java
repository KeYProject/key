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


public class TextualJMLFieldDecl extends TextualJMLConstruct {
    
    private final PositionedString decl;
    
    
    public TextualJMLFieldDecl(ListOfString mods, PositionedString decl) {
        super(mods);
        assert decl != null;
        this.decl = decl;
    }
    
    
    public PositionedString getDecl() {
        return decl;
    }
    
    
    public String toString() {
        return decl.toString();
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLFieldDecl)) {
            return false;
        }
        TextualJMLFieldDecl fd = (TextualJMLFieldDecl) o;
        return mods.equals(fd.mods) && decl.equals(fd.decl);
    }
    
    
    public int hashCode() {
        return mods.hashCode() + decl.hashCode();
    }
}
