// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.speclang.PositionedString;


public final class TextualJMLSpecCase extends TextualJMLConstruct {

    private final Behavior behavior;
    private ImmutableList<PositionedString> requires     
            = ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> assignable   
            = ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> accessible   
            = ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> ensures      
            = ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> signals      
            = ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> signalsOnly 
            = ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> diverges     
            = ImmutableSLList.<PositionedString>nil();
    private PositionedString name = new PositionedString("");

    
    public TextualJMLSpecCase(ImmutableList<String> mods, Behavior behavior) {
        super(mods);
        assert behavior != null;
        this.behavior = behavior;
    }
    
    public void addName(PositionedString n) {
	this.name = n;
    }

    public void addRequires(PositionedString ps) {
        requires = requires.append(ps);
    }
    

    public void addRequires(ImmutableList<PositionedString> l) {
        requires = requires.append(l);
    }
    
    
    public void addAssignable(PositionedString ps) {
        assignable = assignable.append(ps);
    }
    
    
    public void addAccessible(PositionedString ps) {
	accessible = accessible.append(ps);
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
    
    
    public ImmutableList<PositionedString> getRequires() {
        return requires;
    }
    
    
    public ImmutableList<PositionedString> getAssignable() {
        return assignable;
    }
    
    
    public ImmutableList<PositionedString> getAccessible() {
        return accessible;
    }

    
    public ImmutableList<PositionedString> getEnsures() {
        return ensures;
    }

    public PositionedString getName() {
	return name;
    }

    public ImmutableList<PositionedString> getSignals() {
        return signals;
    }
    

    public ImmutableList<PositionedString> getSignalsOnly() {
        return signalsOnly;
    }
    

    public ImmutableList<PositionedString> getDiverges() {
        return diverges;
    }
    
    
    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator<PositionedString> it;
        
        sb.append(behavior + "\n");
        it = requires.iterator();
        while(it.hasNext()) {
            sb.append("requires: " + it.next() + "\n");
        }
        it = assignable.iterator();
        while(it.hasNext()) {
            sb.append("assignable: " + it.next() + "\n");
        }
        it = accessible.iterator();
        while(it.hasNext()) {
            sb.append("accessible: " + it.next() + "\n");
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
    
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLSpecCase)) {
            return false;
        }
        TextualJMLSpecCase sc = (TextualJMLSpecCase) o;
        return mods.equals(sc.mods)
               && behavior.equals(sc.behavior)
               && requires.equals(sc.requires)
               && assignable.equals(sc.assignable)
               && accessible.equals(sc.accessible)               
               && ensures.equals(sc.ensures)
               && signals.equals(sc.signals)
               && signalsOnly.equals(sc.signalsOnly)
               && diverges.equals(sc.diverges);
    }
    
    
    @Override
    public int hashCode() {
        return mods.hashCode()
               + behavior.hashCode()
               + requires.hashCode()
               + assignable.hashCode()
               + accessible.hashCode()               
               + ensures.hashCode()
               + signals.hashCode()
               + signalsOnly.hashCode()
               + diverges.hashCode();
    }
}
