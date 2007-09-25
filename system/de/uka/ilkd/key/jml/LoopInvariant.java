// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.jml;

import java.util.LinkedHashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.SetAsListOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.LocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class LoopInvariant extends JMLSpec implements AssignableSpec {

    private Services services;

    // contains an assignable keyword (like nothing, everithing, ...), 
    // if one occurd in the specification.
    private String assignableMode = null;
    protected SetOfLocationDescriptor assignableLocations 
            = SetAsListOfLocationDescriptor.EMPTY_SET;

    private LoopStatement loop;

    private Term variant = null;
    private Term invariant = null;

    private Term workingSpace = null;

    //post condition for loop. Only used by VBT specific rules.
    private Term post;

    private LinkedHashMap term2old;

    private TermBuilder df = TermBuilder.DF;
    
    private final ProgramVariable selfVar;

    public LoopInvariant(LoopStatement loop, Services services, ProgramVariable selfVar){
	this.services = services;
	post = invariant = df.tt();
	this.loop = loop;
	this.term2old = new LinkedHashMap();
	this.selfVar = selfVar;
    }

    public void addInvariant(Term t){
	invariant = df.and(invariant, t);
    }

    public void setVariant(Term t){
	variant = t;
    }

    public Term getInvariant(){
	return invariant;
    }

    public Term getVariant(){
	return variant;
    }

    public LoopStatement getLoop(){
	return loop;
    }

    public void register(){
	services.getImplementation2SpecMap().addLoopSpec(this);
    }

    public void addAssignable(SetOfLocationDescriptor locations){
	assignableLocations = assignableLocations.union(locations);
    }

    public void addAssignable(LocationDescriptor location){       
        assignableLocations = assignableLocations.add(location);
    }

    public SetOfLocationDescriptor getAssignable(){
	return assignableLocations;
    }

    public void setAssignableMode(String s){
	assignableMode = s;
    }

    public LinkedHashMap getTerm2Old(){
	return term2old;
    }

    public void addPost(Term t){
	if(t != null){
	    post = tf.createJunctorTermAndSimplify(Op.AND, post, t);
	}
    }

    public Term getPost(){
	return post;
    }

    public String getAssignableMode(){
	if(assignableLocations.size() == 0 && assignableMode == null){
	    return "everything";
	}
	// an inconsistent case
	if(assignableLocations.size() > 0 &&
	   "nothing".equals(assignableMode)){
	    return null;
	}
	return assignableMode;
    }
    
    public ProgramVariable getSelfVar() {
	return selfVar;
    }

    public Term getWorkingSpace() {
        return workingSpace;
    }

    public void setWorkingSpace(Term workingSpace) {
        this.workingSpace = workingSpace;
    }

}
