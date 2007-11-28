// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.annotation;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ArrayOfTerm;
import de.uka.ilkd.key.logic.IteratorOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetAsListOfLocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class LoopInvariantAnnotation implements Annotation {

    private final Term invariant;
    private final Term variant;
    private final Term post;
    private final SetOfLocationDescriptor assignable;
    // array containing terms at indices 2n and program variables for
    // storing the initial values of these terms at indices 2n+1 
    // (for 0<=n<olds.size()/2). 
    private final ArrayOfTerm olds;
    private final ProgramVariable selfVar;

    public LoopInvariantAnnotation(Term invariant, 
                                   SetOfLocationDescriptor assignable, 
				   ArrayOfTerm olds, 
                                   Term variant, 
				   Term post,
				   ProgramVariable selfVar){
	this.invariant = invariant;
	this.variant = variant;
	this.post = post;
	this.assignable = assignable == null ? SetAsListOfLocationDescriptor.EMPTY_SET : assignable;
	this.olds = olds == null ? new ArrayOfTerm() :  olds;
	this.selfVar = selfVar;
    }    

    public Term invariant(){
	return invariant;
    }

    public Term variant(){
	return variant;
    }

    public Term post(){
	return post;
    }

    public SetOfLocationDescriptor assignable(){
	return assignable;
    }

    public ArrayOfTerm olds(){
	return olds;
    }
    
    public ProgramVariable getSelfVar() {
	return selfVar;
    }

    public String toString(){
	String result = "invariant: "+invariant+"\nvariant: "+variant+
	    "\nassignable: ";
        IteratorOfLocationDescriptor it = assignable.iterator();
        while(it.hasNext()) {
            result += " "+it.next();
        }
	result += "\nold: "+olds;
	for(int i=0; i<olds.size(); i++){
	    result += olds.getTerm(i)+(i%2==0? "=": " ");
	}
	return result;
    }
    
    public SourceElement getFirstElement(){
        return null;
    }

    public SourceElement getLastElement(){
        return null;
    }

    public Position getStartPosition(){
        return null;
    }

    public Position getEndPosition(){
        return null;
    }

    public Position getRelativePosition(){
        return null;
    }
    
    public PositionInfo getPositionInfo(){
        return null;
    }

    public void visit(Visitor v){
        // do nothing
    }
    
    public void prettyPrint(PrettyPrinter w) throws java.io.IOException{
        // do nothing
    }

    public boolean equalsModRenaming(SourceElement se, 
                                     NameAbstractionTable nat){
        return false;
    }
}
