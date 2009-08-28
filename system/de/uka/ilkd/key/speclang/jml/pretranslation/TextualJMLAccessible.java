// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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


public final class TextualJMLAccessible extends TextualJMLConstruct {
    
    private final PositionedString accessible;
    
    
    public TextualJMLAccessible(ImmutableList<String> mods,
	                        PositionedString represents) {
        super(mods);
        assert represents != null;
        this.accessible = represents;
    }
    
    
    public PositionedString getAccessible() {
        return accessible;
    }
    
    @Override
    public String toString() {
        return accessible.toString();
    }
    
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLAccessible)) {
            return false;
        }
        TextualJMLAccessible a = (TextualJMLAccessible) o;
        return mods.equals(a.mods) && accessible.equals(a.accessible);
    }
    
    
    @Override
    public int hashCode() {
        return mods.hashCode() + accessible.hashCode();
    }
}
