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
import de.uka.ilkd.key.speclang.IteratorOfPositionedString;
import de.uka.ilkd.key.speclang.ListOfPositionedString;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SLListOfPositionedString;


public class TextualJMLSpecCase extends TextualJMLConstruct {

    private final Behavior behavior;
    private ListOfPositionedString requires     
            = SLListOfPositionedString.EMPTY_LIST;
    private ListOfPositionedString assignable   
            = SLListOfPositionedString.EMPTY_LIST;
    private ListOfPositionedString ensures      
            = SLListOfPositionedString.EMPTY_LIST;
    private ListOfPositionedString signals      
            = SLListOfPositionedString.EMPTY_LIST;
    private ListOfPositionedString signalsOnly 
            = SLListOfPositionedString.EMPTY_LIST;
    private ListOfPositionedString diverges     
            = SLListOfPositionedString.EMPTY_LIST;
    private PositionedString name = new PositionedString("");

    
    public TextualJMLSpecCase(ListOfString mods, Behavior behavior) {
        super(mods);
        assert behavior != null;
        this.behavior = behavior;
    }
    
    public void addName(PositionedString name) {
	this.name = name;
    }

    public void addRequires(PositionedString ps) {
        requires = requires.append(ps);
    }
    

    public void addRequires(ListOfPositionedString l) {
        requires = requires.append(l);
    }
    

    public void addAssignable(PositionedString ps) {
        assignable = assignable.append(ps);
    }
    
    
    public void addEnsures(PositionedString ps) {
        ensures = ensures.append(ps);
    }

    
    public void addSignals(PositionedString ps) {
        signals = signals.append(ps);
    }
    

    public void addSignalsOnly(PositionedString ps) {
        signalsOnly = signalsOnly.append(ps);
    }
    

    public void addDiverges(PositionedString ps) {
        diverges = diverges.append(ps);
    }
    

    public Behavior getBehavior() {
        return behavior;
    }
    
    
    public ListOfPositionedString getRequires() {
        return requires;
    }

    
    public ListOfPositionedString getAssignable() {
        return assignable;
    }

    
    public ListOfPositionedString getEnsures() {
        return ensures;
    }

    public PositionedString getName() {
	return name;
    }

    public ListOfPositionedString getSignals() {
        return signals;
    }
    

    public ListOfPositionedString getSignalsOnly() {
        return signalsOnly;
    }
    

    public ListOfPositionedString getDiverges() {
        return diverges;
    }
    
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        IteratorOfPositionedString it;
        
        sb.append(behavior + "\n");
        it = requires.iterator();
        while(it.hasNext()) {
            sb.append("requires: " + it.next() + "\n");
        }
        it = assignable.iterator();
        while(it.hasNext()) {
            sb.append("assignable: " + it.next() + "\n");
        }
        it = ensures.iterator();
        while(it.hasNext()) {
            sb.append("ensures: " + it.next() + "\n");
        }
        it = signals.iterator();
        while(it.hasNext()) {
            sb.append("signals: " + it.next() + "\n");
        }
        it = signalsOnly.iterator();
        while(it.hasNext()) {
            sb.append("signals_only: " + it.next() + "\n");
        }
        it = diverges.iterator();
        while(it.hasNext()) {
            sb.append("diverges: " + it.next() + "\n");
        }
        
        return sb.toString();
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLSpecCase)) {
            return false;
        }
        TextualJMLSpecCase sc = (TextualJMLSpecCase) o;
        return mods.equals(sc.mods)
               && behavior.equals(sc.behavior)
               && requires.equals(sc.requires)
               && assignable.equals(sc.assignable)
               && ensures.equals(sc.ensures)
               && signals.equals(sc.signals)
               && signalsOnly.equals(sc.signalsOnly)
               && diverges.equals(sc.diverges);
    }
    
    
    public int hashCode() {
        return mods.hashCode()
               + behavior.hashCode()
               + requires.hashCode()
               + assignable.hashCode()
               + ensures.hashCode()
               + signals.hashCode()
               + signalsOnly.hashCode()
               + diverges.hashCode();
    }
}
