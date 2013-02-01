// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
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
 * A JML depends / accessible clause for a model field in textual form.
 * Note that such clauses for *methods* are part of TextualJMLSpecCase.
 */
public final class TextualJMLDepends extends TextualJMLConstruct {
    
    private final PositionedString depends;
    
    
    public TextualJMLDepends(ImmutableList<String> mods,
	                     PositionedString depends) {
        super(mods);
        assert depends != null;
        this.depends = depends;
    }
    
    
    public PositionedString getDepends() {
        return depends;
    }
    
    @Override
    public String toString() {
        return depends.toString();
    }
    
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLDepends)) {
            return false;
        }
        TextualJMLDepends a = (TextualJMLDepends) o;
        return mods.equals(a.mods) && depends.equals(a.depends);
    }
    
    
    @Override
    public int hashCode() {
        return mods.hashCode() + depends.hashCode();
    }
}
