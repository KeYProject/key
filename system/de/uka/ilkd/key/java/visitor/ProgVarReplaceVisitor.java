// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.visitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.annotation.Annotation;
import de.uka.ilkd.key.java.annotation.LoopInvariantAnnotation;
import de.uka.ilkd.key.java.declaration.ArrayOfVariableSpecification;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 * Walks through a java AST in depth-left-first-order. This visitor
 * replaces a number of program variables by others or new ones.
 */
public class ProgVarReplaceVisitor extends CreatingASTVisitor {

    private ProgramElement result=null;

    // indicates if ALL program variables are to be replace by new
    // variables with the same name
    protected boolean replaceallbynew=true;

    /**
     * stores the program variables to be replaced as keys and the new
     * program variables as values
     */
    protected Map replaceMap;

    /**
     * creates a visitor that replaces the program variables in the given
     * statement by new ones with the same name
     * @param st the statement where the prog vars are replaced
     * @param oldPVs the program variables that are replaced
     */
    public ProgVarReplaceVisitor(ProgramElement st, ProgramVariable[] oldPVs) {
	super(st, true);
	replaceMap=new HashMap();
	for (int i=0; i<oldPVs.length; i++) {
	    replaceMap.put(oldPVs[i], copy(oldPVs[i]));		
	}
    }

    /**
     * creates a visitor that replaces the program variables in the given
     * statement by new ones with the same name
     * @param st the statement where the prog vars are replaced
     * @param map the HashMap with the replacements
     */
    public ProgVarReplaceVisitor(ProgramElement st, Map map) {
	super(st, true);
	replaceMap = map;
    }

    /**
     * creates a visitor that replaces the program variables in the given
     * statement
     * @param st the statement where the prog vars are replaced
     * @param map the HashMap with the replacements
     * @param replaceall decides if all variables are to be replaced
     */
    public ProgVarReplaceVisitor(ProgramElement st, Map map, boolean replaceall) {
        this(st, map);
        replaceallbynew = replaceall;
    }
        
    /**
     * creates a visitor that replaces the program variables in the given
     * statement by new ones with the same name
     * @param st the statement where the prog vars are replaced
     */
    public ProgVarReplaceVisitor(ProgramElement st) {
	this(st, new HashMap());
    }

    //%%% HACK: there should be a central facility for introducing new program
    // variables; this method is also used in <code>MethodCall</code> to
    // create copies of parameter variables
    public static ProgramVariable copy(ProgramVariable pv) {
	return copy(pv, "");
    }

    //%%% HACK: there should be a central facility for introducing new program
    // variables; this method is also used in <code>MethodCall</code> to
    // create copies of parameter variables
    public static ProgramVariable copy(ProgramVariable pv, String postFix) {
    	ProgramElementName name = pv.getProgramElementName();
	return new LocationVariable
	    (VariableNamer.parseName(name.toString() + postFix,
	    			     name.getCreationInfo()),
	     pv.getKeYJavaType());
    }


    protected void walk(ProgramElement node) {
	if (node instanceof LocalVariableDeclaration && replaceallbynew) {
	    LocalVariableDeclaration vd= (LocalVariableDeclaration)node;
	    ArrayOfVariableSpecification vspecs=vd.getVariableSpecifications();
	    for (int i=0; i<vspecs.size(); i++) {
		ProgramVariable pv 
		    = (ProgramVariable) 
		         vspecs.getVariableSpecification(i).getProgramVariable();
		if (!replaceMap.containsKey(pv)) {
		    replaceMap.put(pv, copy(pv));
		}
	    }
	}
	super.walk(node);
    }

    /** the action that is performed just before leaving the node the
     * last time 
     */
    protected void doAction(ProgramElement node) {
	node.visit(this);
    }
    
    /** starts the walker*/
    public void start() {	
	stack.push(new ExtList());		
	walk(root());
	ExtList el= stack.peek();
	int i=0;
	while (!(el.get(i) instanceof ProgramElement)) {
	    i++;
	}
	result=(ProgramElement) stack.peek().get(i);
    }

    public ProgramElement result() { 	
	return result;
    }
    
    public void performActionOnProgramVariable(ProgramVariable pv) {
	ProgramElement newPV = (ProgramElement) replaceMap.get(pv);
	if (newPV!=null) {
	    addChild(newPV);
	    changed();
	} else {
	    doDefaultAction(pv);
	}
    }

    /**
     * Performs action on the annotations <code>a</code>.
     */
    protected void performActionOnAnnotationArray(Annotation[] a){
	for(int i = 0; i<a.length; i++){
	    if(a[i] instanceof LoopInvariantAnnotation){
		LoopInvariantAnnotation lia = (LoopInvariantAnnotation) a[i];	      
                Term newInvariant   = lia.invariant() == null ? null : 
		    replaceVariablesInTerm(lia.invariant());
                SetOfLocationDescriptor newAssignable = lia.assignable() == null ? 
		    null : replaceVariablesInLocs(lia.assignable());
                ArrayOfTerm newOlds = lia.olds()    == null ? null : replaceVariablesInTerms(lia.olds());
                Term newVariant     = lia.variant() == null ? null : replaceVariablesInTerm(lia.variant());
                Term newPost        = lia.variant() == null ? null : replaceVariablesInTerm(lia.post());
                ProgramVariable newSelfVar = (ProgramVariable)replaceMap.get(lia.getSelfVar());
                if(newSelfVar == null) {
                    newSelfVar = lia.getSelfVar();
                }
                LoopInvariantAnnotation newLia 
                    = new LoopInvariantAnnotation(newInvariant, 
                                                  newAssignable,
                                                  newOlds, 
                                                  newVariant,
						  newPost,
						  newSelfVar);
                
		addToTopOfStack(newLia);
	    }else{
		addToTopOfStack(a[i]);
	    }
	}
	if(a.length>0){
	    changed();
	}
    }

    private Term replaceVariablesInTerm(Term t){  
     	if(t==null) return null;
	if (t.op() instanceof ProgramVariable){ 
	    if (replaceMap.containsKey(t.op())){
		Object o = replaceMap.get(t.op());
		if(o instanceof ProgramVariable){
		    return TermFactory.DEFAULT.createVariableTerm
			((ProgramVariable) replaceMap.get(t.op()));
		}else{
		    return TermFactory.DEFAULT.createVariableTerm
			((SchemaVariable) replaceMap.get(t.op()));
		}
	    }else{
		return t;
	    }
	} else {
	    Term subTerms[] = new Term[t.arity()];
	    ArrayList vars = new ArrayList();
	    for ( int i = 0; i<t.arity(); i++ ) {
		ArrayOfQuantifiableVariable vbh = t.varsBoundHere(i);
		for( int j=0; j<vbh.size(); j++ ) {
		    vars.add(vbh.getQuantifiableVariable(j));
		}
		subTerms[i] = replaceVariablesInTerm(t.sub(i));
	    }
	    Operator op;
	    if(t.op() instanceof IUpdateOperator){
		IUpdateOperator uo = (IUpdateOperator) t.op();
		ListOfLocation locs = SLListOfLocation.EMPTY_LIST;
		for(int i = 0; i<uo.locationCount(); i++){
		    if (replaceMap.containsKey(uo.location(i))){ 
			locs = locs.append((Location)
					   replaceMap.
					   get(uo.location(i)));
		    }else{
			locs = locs.append(uo.location(i));
		    }
		}
		op = uo.replaceLocations ( locs.toArray () );
	    }else{
		op = t.op();
	    }
	    QuantifiableVariable v1[] = new QuantifiableVariable[0];
	    v1 = (QuantifiableVariable[])(vars.toArray(v1));
	    JavaBlock jb = t.javaBlock();
	    return TermFactory.DEFAULT.createTerm(op,subTerms,v1,jb);
	}
    }

    
    private SetOfLocationDescriptor replaceVariablesInLocs(
                                                SetOfLocationDescriptor locs) {
        SetOfLocationDescriptor res 
            = SetAsListOfLocationDescriptor.EMPTY_SET;
        
        IteratorOfLocationDescriptor it = locs.iterator();
        while(it.hasNext()) {
            LocationDescriptor loc = it.next();
            LocationDescriptor newLoc;
            
            if(loc instanceof BasicLocationDescriptor) {
                BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
                Term newFormula = replaceVariablesInTerm(bloc.getFormula());
                Term newLocTerm = replaceVariablesInTerm(bloc.getLocTerm());
                newLoc = new BasicLocationDescriptor(newFormula, newLocTerm);
            } else {
                Debug.assertTrue(loc instanceof EverythingLocationDescriptor);
                newLoc = loc;
            }
            
            res = res.add(newLoc);
        }
        
        return res;
    }
    
    
    private ArrayOfTerm replaceVariablesInTerms(ArrayOfTerm terms) {
        Term[] res = new Term[terms.size()];

        for(int i = 0; i < res.length; i++) {
            res[i] = replaceVariablesInTerm(terms.getTerm(i));
        }
        
        return new ArrayOfTerm(res);
    }

    public void performActionOnLocationVariable(LocationVariable x) {
       performActionOnProgramVariable(x);
    }

    public void performActionOnProgramConstant(ProgramConstant x) {
        performActionOnProgramVariable(x);
    }
}
