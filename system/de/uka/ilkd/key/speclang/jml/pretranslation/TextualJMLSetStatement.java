// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.speclang.PositionedString;


public class TextualJMLSetStatement extends TextualJMLConstruct {
    
    private final PositionedString assignment;
    
    
    public TextualJMLSetStatement(ImmutableList<String> mods, 
                                  PositionedString assignment) {
        super(mods);
        assert assignment != null;
        this.assignment = assignment;
    }
    
    
    public PositionedString getAssignment() {
        return assignment;
    }
    
    
    public String toString() {
        return assignment.toString();
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLSetStatement)) {
            return false;
        }
        TextualJMLSetStatement ss = (TextualJMLSetStatement) o;
        return mods.equals(ss.mods) && assignment.equals(ss.assignment);
    }
    
    
    public int hashCode() {
        return mods.hashCode() + assignment.hashCode();
    }
}
