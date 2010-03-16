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


public class TextualJMLSpecCase extends TextualJMLConstruct {

    private final Behavior behavior;
    private PositionedString workingSpace = null;
    private PositionedString constructedWorkingSpace = null;
    private PositionedString reentrantWorkingSpace = null;
    private PositionedString callerWorkingSpace = null;


    
    private ImmutableList<PositionedString> requires     
            = ImmutableSLList.<PositionedString>nil();
    private ImmutableList<PositionedString> assignable   
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
    
    public void addName(PositionedString name) {
	this.name = name;
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
    
    
    public void addEnsures(PositionedString ps) {
        ensures = ensures.append(ps);
    }

    
    public void addSignals(PositionedString ps) {
        signals = signals.append(ps);
    }
    

    public void addSignalsOnly(PositionedString ps) {
        signalsOnly = signalsOnly.append(ps);
    }
    
    public void setWorkingSpace(PositionedString ps){
        workingSpace = ps;
    }
    
    public void setLocalWorkingSpace(PositionedString ps){
        workingSpace = ps;
    }
    
    public void setConstructedWorkingSpace(PositionedString ps){
        constructedWorkingSpace = ps;
    }
    
    public void setCallerWorkingSpace(PositionedString ps){
        callerWorkingSpace = ps;
    }
    
    public void setReentrantWorkingSpace(PositionedString ps){
        reentrantWorkingSpace = ps;
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
    
    public PositionedString getWorkingSpace(){
        return workingSpace;
    }
    
    public PositionedString getLocalWorkingSpace(){
        return workingSpace;
    }
    
    public PositionedString getConstructedWorkingSpace(){
        return constructedWorkingSpace;
    }
    
    public PositionedString getCallerWorkingSpace(){
        return callerWorkingSpace;
    }
    
    public PositionedString getReentrantWorkingSpace(){
        return reentrantWorkingSpace;
    }
    
    public ImmutableList<PositionedString> getDiverges() {
        return diverges;
    }
    
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator<PositionedString> it;

        sb.append(behavior).append("\n");
        it = requires.iterator();
        while(it.hasNext()) {
            sb.append("requires: ").append(it.next()).append("\n");
        }
        it = assignable.iterator();
        while(it.hasNext()) {
            sb.append("assignable: ").append(it.next()).append("\n");
        }
        it = ensures.iterator();
        while(it.hasNext()) {
            sb.append("ensures: ").append(it.next()).append("\n");
        }
        it = signals.iterator();
        while(it.hasNext()) {
            sb.append("signals: ").append(it.next()).append("\n");
        }
        it = signalsOnly.iterator();
        while(it.hasNext()) {
            sb.append("signals_only: ").append(it.next()).append("\n");
        }
        it = diverges.iterator();
        while(it.hasNext()) {
            sb.append("diverges: ").append(it.next()).append("\n");
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
