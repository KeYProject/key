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


public class TextualJMLMethodDecl extends TextualJMLConstruct {
    
    private final PositionedString decl;
    private final String methodName;
    
    
    public TextualJMLMethodDecl(ListOfString mods, 
                                PositionedString decl, 
                                String methodName) {
        super(mods);
        assert decl != null;
        this.decl = decl;
        this.methodName = methodName;
    }
    
    
    public PositionedString getDecl() {
        return decl;
    }
    
    
    public String getMethodName() {
        return methodName;
    }
    
    
    public String toString() {
        return decl.toString();
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLMethodDecl)) {
            return false;
        }
        TextualJMLMethodDecl md = (TextualJMLMethodDecl) o;
        return mods.equals(md.mods) 
               && decl.equals(md.decl) 
               && methodName.equals(md.methodName);
    }
    
    
    public int hashCode() {
        return mods.hashCode() + decl.hashCode() + methodName.hashCode();
    }
}
