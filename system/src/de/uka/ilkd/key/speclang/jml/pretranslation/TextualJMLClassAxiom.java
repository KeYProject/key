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
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.speclang.PositionedString;


/**
 * A JML axiom declaration in textual form.
 * According to Sect. 8 of the JML reference manual, axioms may not have any modifiers.
 */
public final class TextualJMLClassAxiom extends TextualJMLConstruct {
    
    private final PositionedString inv;
    
    /** new textual representation.
     * @param mods modifiers (are currently ignored)
     * @param inv the expression in this clause
     */
    public TextualJMLClassAxiom(ImmutableList<String> mods, 
	                      PositionedString inv) {
        super(ImmutableSLList.<String>nil()); // no modifiers allowed in axiom clause (see Sect. 8 of reference manual)
        assert inv != null;
        this.inv = inv;
    }
    
    public TextualJMLClassAxiom(ImmutableList<String> mods, PositionedString inv, String name){
        this(mods,inv);
        this.name = name;
    }
    
    
    public PositionedString getAxiom() {
        return inv;
    }
    
    
    @Override
    public String toString() {
        return inv.toString();
    }
    
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLClassAxiom)) {
            return false;
        }
        TextualJMLClassAxiom ci = (TextualJMLClassAxiom) o;
        return mods.equals(ci.mods) && inv.equals(ci.inv);
    }
    
    
    @Override
    public int hashCode() {
        return mods.hashCode() + inv.hashCode();
    }
    
    public String getName(){
        return name;
    }
}