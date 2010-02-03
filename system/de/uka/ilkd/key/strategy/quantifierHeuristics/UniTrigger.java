// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.quantifierHeuristics;



import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IteratorOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.ListOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.MapFromQuantifiableVariableToTerm;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SLListOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;
import de.uka.ilkd.key.util.LRUCache;


class UniTrigger extends Trigger {
  
    private final Term trigger;
    private final SetOfQuantifiableVariable uqvs;
    
    private final TriggersSet triggerSetThisBelongsTo;
    
    private final boolean onlyUnify;
    private final boolean isElementOfMultitrigger;
   
    private final LRUCache<Term, SetOfSubstitution> matchResults = new LRUCache<Term, SetOfSubstitution> ( 1000 );
    
    UniTrigger(Term trigger,SetOfQuantifiableVariable uqvs,
               boolean isUnify,boolean isElementOfMultitrigger,
               TriggersSet triggerSetThisBelongsTo){
        this.trigger = trigger;
        this.uqvs=uqvs;
        this.onlyUnify=isUnify;
        this.isElementOfMultitrigger=isElementOfMultitrigger;
        this.triggerSetThisBelongsTo = triggerSetThisBelongsTo;
    }
        
    public SetOfSubstitution getSubstitutionsFromTerms(SetOfTerm targetTerm, 
            Services services) {
        SetOfSubstitution allsubs = SetAsListOfSubstitution.EMPTY_SET;
        final IteratorOfTerm it = targetTerm.iterator ();
        while ( it.hasNext () )
            allsubs = allsubs.union ( getSubstitutionsFromTerm ( it.next (), services ) );
        return allsubs;
    }

    private SetOfSubstitution getSubstitutionsFromTerm(Term t, Services services) {
        SetOfSubstitution res = matchResults.get ( t );
        if ( res == null ) {
            res = getSubstitutionsFromTermHelp ( t, services );
            matchResults.put ( t, res );
        }
        return res;
    }

    private SetOfSubstitution getSubstitutionsFromTermHelp(Term t, Services services) {
        SetOfSubstitution newSubs = SetAsListOfSubstitution.EMPTY_SET;
        if ( t.freeVars ().size () > 0 || t.op () instanceof Quantifier )
            newSubs = Matching.twoSidedMatching ( this, t, services );
        else if ( !onlyUnify )
            newSubs = Matching.basicMatching ( this, t );
        return newSubs;
    }

    
    public Term getTriggerTerm() {
        return trigger;
    }

    public boolean equals(Object arg0) {
        if (!(arg0 instanceof UniTrigger)) return false;
        final UniTrigger a = (UniTrigger) arg0;
        return a.trigger.equals(trigger);
    }
    public int hashCode() {
        return trigger.hashCode();
    }
    public String toString() {
        return "" + trigger;
    }

    SetOfQuantifiableVariable getUniVariables() {
        return uqvs;
    }

    public TriggersSet getTriggerSetThisBelongsTo() {
        return triggerSetThisBelongsTo;
    }

    
    
    /**
     * use similar algorithm as basic matching to detect loop
     * 
     * @param candidate
     * @param searchTerm
     */
    public static boolean passedLoopTest(Term candidate, Term searchTerm) {
        final SetOfSubstitution substs =
            BasicMatching.getSubstitutions ( candidate, searchTerm );

        final IteratorOfSubstitution it = substs.iterator ();
        while ( it.hasNext () ) {
            final Substitution subst = it.next ();
            if ( containsLoop ( subst ) ) return false;
        }
        return true;
    }
    
     /**
     * Test whether this substitution constains loop.
     * It is mainly used for unitrigger's loop test.
     */
    private static boolean containsLoop(Substitution subst) {
        final IteratorOfQuantifiableVariable it = subst.getVarMap().keyIterator ();
        while ( it.hasNext () ) {
            if ( containsLoop ( subst.getVarMap(), it.next () ) ) return true;
        }
        return false;
    } 
    
    /**
     * Code copied from logic.EqualityConstraint
     */
    private static boolean containsLoop(MapFromQuantifiableVariableToTerm varMap,
                                        QuantifiableVariable var) {
        ListOfQuantifiableVariable body          =
            SLListOfQuantifiableVariable.EMPTY_LIST;
        ListOfTerm                 fringe        = SLListOfTerm.EMPTY_LIST;
        Term                       checkForCycle = varMap.get( var );
        
        if ( checkForCycle.op () == var ) return false;
        
        while ( true ) {
            final IteratorOfQuantifiableVariable it =
                                checkForCycle.freeVars ().iterator ();
            while ( it.hasNext () ) {
                final QuantifiableVariable termVar = it.next ();
                if ( !body.contains ( termVar ) ) {
                    final Term termVarterm = varMap.get( termVar );
                    if ( termVarterm != null ) {
                        if ( termVarterm.freeVars ().contains ( var ) )
                            return true;
                        fringe = fringe.prepend ( termVarterm );                        
                    }
                    
                    if ( termVar == var ) return true;

                    body = body.prepend ( termVar );
                }
            }

            if ( fringe == SLListOfTerm.EMPTY_LIST ) return false;

            checkForCycle = fringe.head ();
            fringe        = fringe.tail ();
        }
    }

    boolean isElementOfMultitrigger() {
        return isElementOfMultitrigger;
    }


}
     
