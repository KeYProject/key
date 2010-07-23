// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.visitor;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.speclang.LocationDescriptorSet;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.speclang.LoopPredicateSet;
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
     * @param map the HashMap with the replacements
     */
    public ProgVarReplaceVisitor(ProgramElement st, Map map, Services services) {
	super(st, true, services);
	this.replaceMap = map;
        assert services != null;
    }
    

    /**
     * creates a visitor that replaces the program variables in the given
     * statement
     * @param st the statement where the prog vars are replaced
     * @param map the HashMap with the replacements
     * @param replaceall decides if all variables are to be replaced
     */
    public ProgVarReplaceVisitor(ProgramElement st, 
                                 Map map, 
                                 boolean replaceall, 
                                 Services services) {
        this(st, map, services);
        this.replaceallbynew = replaceall;
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
    	//%%% HACK: final local variables are not renamed since they can occur in an
    	// anonymous class declared in their scope of visibility.
/*    	if(pv.isFinal()){
    	    return pv;
    	}*/
	return new LocationVariable
	    (VariableNamer.parseName(name.toString() + postFix,
	    			     name.getCreationInfo()),
	     pv.getKeYJavaType(), pv.isFinal());
    }


    protected void walk(ProgramElement node) {
	if (node instanceof LocalVariableDeclaration && replaceallbynew) {
	    LocalVariableDeclaration vd= (LocalVariableDeclaration)node;
	    ImmutableArray<VariableSpecification> vspecs=vd.getVariableSpecifications();
	    for (int i=0; i<vspecs.size(); i++) {
		ProgramVariable pv 
		    = (ProgramVariable) 
		         vspecs.get(i).getProgramVariable();
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
	    final ImmutableArray<QuantifiableVariable>[] vars = new ImmutableArray[t.arity()]; 
	    for ( int i = 0; i<t.arity(); i++ ) {
		vars[i] = t.varsBoundHere(i);
		subTerms[i] = replaceVariablesInTerm(t.sub(i));
	    }
	    Operator op;
	    if(t.op() instanceof IUpdateOperator){
		IUpdateOperator uo = (IUpdateOperator) t.op();
		final Location[] locs = new Location[uo.locationCount()];
		for(int i = 0; i<locs.length; i++){
		    if (replaceMap.containsKey(uo.location(i))){ 
			locs[i] = (Location) replaceMap.get(uo.location(i));
		    }else{
			locs[i] = uo.location(i);
		    }
		}
		op = uo.replaceLocations ( locs );
	    }else{
		op = t.op();
	    }
	    return TermFactory.DEFAULT.createTerm(op, subTerms, vars, t.javaBlock());
	}
    }

    
    private ImmutableSet<LocationDescriptor> replaceVariablesInLocs(
                                                ImmutableSet<LocationDescriptor> locs) {
        ImmutableSet<LocationDescriptor> res 
            = DefaultImmutableSet.<LocationDescriptor>nil();
        for (final LocationDescriptor loc : locs) {
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
    
        
    private ImmutableSet<Term> replaceVariablesInTerms(ImmutableSet<Term> terms) {
        ImmutableSet<Term> res = DefaultImmutableSet.<Term>nil();        
        for (final Term term : terms) {
            res = res.add(replaceVariablesInTerm(term));
        }        
        return res;
    }
    
    
    private Map /*Operator -> Function*/ replaceVariablesInMap(
                                        Map /*Operator -> Function*/ map) {
        Map result = new LinkedHashMap();
        for (Object o : map.entrySet()) {
            Map.Entry entry = (Map.Entry) o;
            Operator key = (Operator) entry.getKey();
            Function value = (Function) entry.getValue();

            Operator newKey = (ProgramVariable) replaceMap.get(key);
            if (newKey == null) {
                newKey = key;
            }

            result.put(newKey, value);
        }
        return result;
    }
    
    
    public void performActionOnLocationVariable(LocationVariable x) {
       performActionOnProgramVariable(x);
    }

    
    public void performActionOnProgramConstant(ProgramConstant x) {
        performActionOnProgramVariable(x);
    }
    
    
    public void performActionOnLoopInvariant(LoopStatement oldLoop, 
                                             LoopStatement newLoop) {
        LoopInvariant inv 
            = services.getSpecificationRepository().getLoopInvariant(oldLoop);
        if(inv == null) {
            return;
        }
        Term selfTerm = inv.getInternalSelfTerm();
        Map atPreFunctions = inv.getInternalAtPreFunctions();
        
        //invariant
        Term newInvariant 
            = replaceVariablesInTerm(inv.getInvariant(selfTerm, 
                                                      atPreFunctions, 
                                                      services));
        
        //predicates
        ImmutableSet<Term> newPredicates 
            = replaceVariablesInTerms(inv.getPredicates(selfTerm, 
                                                        atPreFunctions, 
                                                        services).asSet());
        
        //modifies
        ImmutableSet<LocationDescriptor> newModifies
            = replaceVariablesInLocs(inv.getModifies(selfTerm, 
                                                     atPreFunctions, 
                                                     services).asSet());
        
        //variant
        Term newVariant
            = replaceVariablesInTerm(inv.getVariant(selfTerm, 
                                                    atPreFunctions, 
                                                    services));
        
        //working spaces
        Term newWorkingSpaceLocal
            = replaceVariablesInTerm(inv.getWorkingSpace(selfTerm, 
                                                    atPreFunctions, 
                                                    services));
        
        Term newParametrizedWS
            = replaceVariablesInTerm(inv.getParametrizedWorkingSpaceTerms(selfTerm, 
                    atPreFunctions, 
                    services));
        
        Term newSelfTerm = replaceVariablesInTerm(selfTerm); 
        Map newAtPreFunctions = replaceVariablesInMap(atPreFunctions);
        boolean newPredicateHeuristicsAllowed
            = inv.getPredicateHeuristicsAllowed();

        LoopInvariant newInv 
            = new LoopInvariantImpl(newLoop, 
                                    newInvariant, 
                                    new LoopPredicateSet(newPredicates),
                                    new LocationDescriptorSet(newModifies), 
                                    newVariant, 
                                    newParametrizedWS,
                                    newWorkingSpaceLocal,
                                    newSelfTerm,
                                    newAtPreFunctions,
                                    newPredicateHeuristicsAllowed);
        services.getSpecificationRepository().setLoopInvariant(newInv);
    }
}
