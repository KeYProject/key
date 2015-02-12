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
 * A JML initially clause declaration in textual form.
 * @author Daniel Bruns
 */
public final class TextualJMLInitially extends TextualJMLConstruct {
    
    private final PositionedString inv;
    
    
    public TextualJMLInitially(ImmutableList<String> mods, 
	                      PositionedString inv) {
        super(mods);
        assert inv != null;
        this.inv = inv;
        setPosition(inv);
    }
    
    public PositionedString getInv() {
        return inv;
    }
    
    
    @Override
    public String toString() {
        return inv.toString();
    }
    
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLInitially)) {
            return false;
        }
        TextualJMLInitially ci = (TextualJMLInitially) o;
        return mods.equals(ci.mods) && inv.equals(ci.inv);
    }
    
    
    @Override
    public int hashCode() {
        return mods.hashCode() + inv.hashCode();
    }
}