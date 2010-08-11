// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/** 
 * A position taclet application object, contains already the information to
 * which term/formula of the sequent the taclet is attached. The position
 * information has been determined by matching the find-part of the
 * corresponding taclet against the term described by the position
 * information. If such a match has not been performed or a taclet is a no find
 * taclet, a no position taclet object ({@link
 * de.uka.ilkd.key.rule.NoPosTacletApp}) is used to keep track of the (partial)
 * instantiation information.
 */
public class PosTacletApp extends TacletApp {

    /** stores the information where the Taclet is to be applied. This means where
     * the find section of the taclet matches
     */
    private final PosInOccurrence pos;

    /** creates a PosTacletApp for the given taclet 
     * and a position information and CHECKS variable conditions as well as it
     * resolves collisions
     * @param taclet the FindTaclet 
     * @param pos the PosInOccurrence storing the position where to apply the 
     * Taclet
     * @return new PosTacletApp or null if conditions (assertions) have been hurted
     */
    public static PosTacletApp createPosTacletApp(FindTaclet taclet, PosInOccurrence pos) { 
	// no instantiations no checks are needed
	return new PosTacletApp(taclet, pos);
    }
    
    /** creates a PosTacletApp for the given taclet with some known instantiations
     * and a position information 
     * and CHECKS variable conditions as well as it resolves
     * collisions
     * The ifInstantiations parameter is not
     * matched against the if sequence, but only stored. For matching
     * use the method "setIfFormulaInstantiations".
     * @param taclet the FindTaclet 
     * @param instantiations the SVInstantiations
     * @param pos the PosInOccurrence storing the position where to apply the 
     * Taclet
     * @return new PosTacletApp or null if conditions (assertions) have been hurted
     */
    public static PosTacletApp
	createPosTacletApp(FindTaclet       taclet, 
			   SVInstantiations instantiations,
			   PosInOccurrence  pos) { 
	return createPosTacletApp ( taclet,
				    instantiations,
				    Constraint.BOTTOM,
				    DefaultImmutableSet.<Metavariable>nil(),
				    null,
				    pos );
    }


    public static PosTacletApp
	createPosTacletApp(FindTaclet         taclet, 
			   SVInstantiations   instantiations,
			   Constraint         matchConstraint,
			   ImmutableSet<Metavariable>  matchNewMetavariables,
			   PosInOccurrence    pos) { 
	return createPosTacletApp ( taclet,
				    instantiations,
				    matchConstraint,
				    matchNewMetavariables,
				    null,
				    pos );	
    }

    public static PosTacletApp
	createPosTacletApp(FindTaclet                   taclet, 
			   SVInstantiations             instantiations,
			   Constraint                   matchConstraint,
			   ImmutableSet<Metavariable>            matchNewMetavariables,
			   ImmutableList<IfFormulaInstantiation> ifInstantiations,
			   PosInOccurrence              pos) { 
	Debug.assertTrue ( ifInstsCorrectSize ( taclet, ifInstantiations ),
			   "If instantiations list has wrong size" );
        
	if ( !matchConstraint.isSatisfiable () )
	    return null;

	instantiations=resolveCollisionWithContext(taclet, resolveCollisionVarSV
						   (taclet, instantiations), pos);
	if (checkVarCondNotFreeIn(taclet, instantiations, pos)) {
	    return new PosTacletApp(taclet,
				    instantiations,
				    matchConstraint,
				    matchNewMetavariables,
				    ifInstantiations,
				    pos);
	}
	
	return null;
    }

    public static PosTacletApp createPosTacletApp(FindTaclet         taclet,
						  MatchConditions    matchCond,
						  PosInOccurrence    pos) {
	return createPosTacletApp ( taclet,
				    matchCond.getInstantiations   (),
				    matchCond.getConstraint       (),
				    matchCond.getNewMetavariables (),
				    null,
				    pos );
    }


    /** creates a PosTacletApp for the given taclet 
     * and a position information
     * @param taclet the FindTaclet 
     * @param pos the PosInOccurrence storing the position where to apply the 
     * Taclet
     */
    private PosTacletApp(FindTaclet taclet, PosInOccurrence pos) { 
	super(taclet);
	this.pos = pos;
    }

    /** creates a PosTacletApp for the given taclet with some known instantiations
     * and a position information
     * @param taclet the FindTaclet 
     * @param pos the PosInOccurrence storing the position where to apply the 
     * Taclet
     * @param instantiations the SVInstantiations
     */
    private PosTacletApp(FindTaclet                   taclet,
			 SVInstantiations             instantiations,
			 Constraint                   matchConstraint,
			 ImmutableSet<Metavariable>            matchNewMetavariables,
			 ImmutableList<IfFormulaInstantiation> ifInstantiations,
			 PosInOccurrence              pos) { 
	super(taclet,
	      instantiations,
	      matchConstraint,
	      matchNewMetavariables,
	      ifInstantiations);
	this.pos = pos;
    }
    
    
    /**
     * returns the LogicVariables that are bound above the
     * PositionInOccurrence of the PosTacletApp. __OPTIMIZE__ If this method 
     * is needed
     * more than once caching the result should be considered.
     *
     * @return the set of the logicvariables that are bound for the
     * indicated application position of the TacletApp.
     */
    private static ImmutableSet<QuantifiableVariable> varsBoundAboveFindPos
	(Taclet taclet, PosInOccurrence pos) {

	if (!(taclet instanceof RewriteTaclet)) {
	    return DefaultImmutableSet.<QuantifiableVariable>nil();
	}

	return collectBoundVarsAbove ( pos );
    }

    private static Iterator<SchemaVariable> allVariableSV(Taclet taclet) {
	TacletVariableSVCollector coll = new TacletVariableSVCollector();
	coll.visit(taclet, true); //__CHANGE__ true or false???
	return coll.varIterator();
    }


    protected ImmutableSet<QuantifiableVariable> contextVars(SchemaVariable sv) {
	if (!taclet().getPrefix(sv).context()) {
	    return DefaultImmutableSet.<QuantifiableVariable>nil();
	}
	return varsBoundAboveFindPos(taclet(), posInOccurrence());
    }


    /**
     * resolves collisions with the context
     * in an SVInstantiation
     *
     * @param insts the original SVInstantiations
     * @return the resolved SVInstantiations
     */
    private static SVInstantiations resolveCollisionWithContext
	(Taclet taclet, SVInstantiations insts, PosInOccurrence pos){	

	if (taclet.isContextInPrefix()) {
	    ImmutableSet<QuantifiableVariable> k=varsBoundAboveFindPos(taclet, pos);
	    Iterator<SchemaVariable> it=allVariableSV(taclet);
	    while (it.hasNext()) {
		SchemaVariable varSV=it.next();
		Term inst=(Term) insts.getInstantiation(varSV);
		if (inst!=null && k.contains((QuantifiableVariable)inst.op())) {
		    insts = replaceInstantiation(taclet, insts, varSV);
		}
	    }
	}
	return insts;
    }


    /** adds a new instantiation to this TacletApp 
     * @param sv the SchemaVariable to be instantiated
     * @param term the Term the SchemaVariable is instantiated with
     * @return the new TacletApp
     */
    public TacletApp addInstantiation(SchemaVariable sv, Term term, 
                                      boolean interesting) {	
                    
        if (interesting)
	    return createPosTacletApp((FindTaclet)taclet(), 
				      instantiations()
				      .addInteresting(sv, term),
				      constraint       (),
				      newMetavariables (),
				      ifFormulaInstantiations (),
				      posInOccurrence  ());
	else
	    return createPosTacletApp((FindTaclet)taclet(), 
				      instantiations().add(sv, term),
				      constraint       (),
				      newMetavariables (),
				      ifFormulaInstantiations (),
				      posInOccurrence  ());
    }

    /** adds a new instantiation to this TacletApp 
     * @param sv the SchemaVariable to be instantiated
     * @param pe the ProgramElement the SV is instantiated with
     * @return the new TacletApp
     */
    public TacletApp addInstantiation(SchemaVariable sv, ProgramElement pe,
                                      boolean interesting) {
	if (interesting)
	    return createPosTacletApp((FindTaclet)taclet(), 
				      instantiations()
				      .addInteresting(sv, pe),
				      constraint       (),
				      newMetavariables (),
				      ifFormulaInstantiations (),
				      posInOccurrence  ());
	else
	    return createPosTacletApp((FindTaclet)taclet(), 
				      instantiations()
				      .add(sv, pe),
				      constraint       (),
				      newMetavariables (),
				      ifFormulaInstantiations (),
				      posInOccurrence  ());
    }
    
    
    
    public TacletApp addInstantiation(SchemaVariable sv, Object[] list,
			boolean interesting) {
		if (interesting)
			return createPosTacletApp((FindTaclet) taclet(), instantiations()
					.addInterestingList(sv, list), constraint(), newMetavariables(),
					ifFormulaInstantiations(), posInOccurrence());
		else
			return createPosTacletApp((FindTaclet) taclet(), instantiations()
					.addList(sv, list), constraint(), newMetavariables(),
					ifFormulaInstantiations(), posInOccurrence());
	}



    /**
     * creates a new Taclet application containing all the
     * instantiations given 
     * by the SVInstantiations and the ones of this TacletApp
     * @param svi the SVInstantiations whose entries are the needed
     * instantiations 
     * @return the new Taclet application
     */
    public TacletApp addInstantiation(SVInstantiations svi) {
	return createPosTacletApp((FindTaclet)taclet(), 
				  svi.union(instantiations()),
				  constraint       (),
				  newMetavariables (),
				  ifFormulaInstantiations (),
				  posInOccurrence  ());
    }


    /**
     * creates a new Taclet application containing all the
     * instantiations given 
     * by the SVInstantiations and forget the old ones.
     * @param svi the SVInstantiations whose entries are the needed
     * instantiations 
     * @return the new Taclet application
     */
    protected TacletApp setInstantiation(SVInstantiations svi) {
	return createPosTacletApp((FindTaclet)taclet(),
				  svi,
				  constraint       (),
				  newMetavariables (),
				  ifFormulaInstantiations (),
				  posInOccurrence  ());
    }


    /**
     * creates a new Taclet application containing all the
     * instantiations, constraints and new metavariables given 
     * by the mc object and forget the old ones
     */
    public TacletApp setMatchConditions ( MatchConditions mc ) {
	return createPosTacletApp( (FindTaclet)taclet(),
				   mc.getInstantiations   (),
				   mc.getConstraint       (),
				   mc.getNewMetavariables (),
				   ifFormulaInstantiations (),
				   posInOccurrence ());
    }


    /**
     * creates a new Taclet application containing all the
     * instantiations, constraints, new metavariables and if formula
     * instantiations given and forget the old ones
     */
    protected TacletApp setAllInstantiations ( MatchConditions              mc,
					       ImmutableList<IfFormulaInstantiation> ifInstantiations ) {
	return createPosTacletApp( (FindTaclet)taclet(),
				   mc.getInstantiations   (),
				   mc.getConstraint       (),
				   mc.getNewMetavariables (),
				   ifInstantiations,
				   posInOccurrence () );
    }


    /** returns true iff all necessary informations are collected, so
     * that the Taclet can be applied.
     * @return true iff all necessary informations are collected, so
     * that the Taclet can be applied.
     */
    public boolean complete() {
	return posInOccurrence() != null && 
	    uninstantiatedVars().isEmpty() &&
	    ifInstsComplete ();
    }


    /**
     * @return true iff the taclet instantiation can be made complete
     * using metavariables
     */
    public boolean sufficientlyComplete() {
	return posInOccurrence() != null &&
	       instsSufficientlyComplete () && ifInstsComplete ();
    }


    /**
     * returns the PositionInOccurrence (representing a ConstrainedFormula and
     * a position in the corresponding formula)
     * @return the PosInOccurrence
     */
    public PosInOccurrence posInOccurrence() {
	return pos;
    }

    public boolean equals(Object o) {
        if (o instanceof PosTacletApp) {
	        return super.equals(o)
	            && ((PosTacletApp)o).posInOccurrence().equals(posInOccurrence());
        }
        return false;
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + super.hashCode();
    	result = 37 * result + posInOccurrence().hashCode();
    	return result;
    }

    public String toString() {
	return super.toString()+" at "+posInOccurrence();
    }

}
