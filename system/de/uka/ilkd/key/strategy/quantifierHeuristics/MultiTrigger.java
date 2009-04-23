// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
///
package de.uka.ilkd.key.strategy.quantifierHeuristics;



import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.EntryOfQuantifiableVariableAndTerm;
import de.uka.ilkd.key.logic.op.IteratorOfEntryOfQuantifiableVariableAndTerm;
import de.uka.ilkd.key.logic.op.MapAsListFromQuantifiableVariableToTerm;
import de.uka.ilkd.key.logic.op.MapFromQuantifiableVariableToTerm;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;


class MultiTrigger extends Trigger {

    private final SetOfTrigger triggers;
    private final SetOfQuantifiableVariable qvs;
    private final Term clause;

    MultiTrigger(SetOfTrigger triggers, 
                 SetOfQuantifiableVariable qvs,Term clause){
        this.triggers = triggers;
        this.qvs = qvs;
        this.clause = clause;
    }
    
    public SetOfSubstitution getSubstitutionsFromTerms(SetOfTerm targetTerms, 
            Services services){
        SetOfSubstitution res = SetAsListOfSubstitution.EMPTY_SET;
        SetOfSubstitution mulsubs = 
        	                setMultiSubstitution(triggers.toArray(),0,targetTerms, 
                                        services);
        IteratorOfSubstitution it = mulsubs.iterator();
        while(it.hasNext()){
        	    Substitution sub = it.next();
            if(sub.isTotalOn(qvs))res=res.add(sub);
        }
        
        return res;
    }
    
    /**help function for getMultiSubstitution*/
    private SetOfSubstitution setMultiSubstitution(Trigger[] ts,int i,
            SetOfTerm terms, Services services){
    	    SetOfSubstitution res = SetAsListOfSubstitution.EMPTY_SET;
    	    if(i>=ts.length)return res;
    	    SetOfSubstitution subi = ts[i].getSubstitutionsFromTerms(terms, services);
            SetOfSubstitution nextSubs = setMultiSubstitution(ts,i+1,terms, services);
            if(nextSubs.size()==0)return res.union(subi);
            IteratorOfSubstitution it = nextSubs.iterator();
            while(it.hasNext()){
                    Substitution sub0= it.next();
                    IteratorOfSubstitution it1 = subi.iterator();
                    while(it1.hasNext()){
                    	Substitution sub1 = unifySubstitution(sub0,it1.next());
                    	if(sub1!=null) res = res.add(sub1);
                    }
                    
            }
            return res;
    }   
    
     
    /**unify two substitution, if same variable are bound with same term return
     * a new substitution with all universal quantifiable variables in two
     *  substituition, otherwise return null*/
    private Substitution unifySubstitution(Substitution sub0,
    		                                Substitution  sub1){
    	IteratorOfEntryOfQuantifiableVariableAndTerm it0 = sub0.getVarMap()
                .entryIterator();
        MapFromQuantifiableVariableToTerm map1 = sub1.getVarMap();
        MapFromQuantifiableVariableToTerm resMap = 
        	                    MapAsListFromQuantifiableVariableToTerm.EMPTY_MAP;

        while (it0.hasNext()) {
            EntryOfQuantifiableVariableAndTerm en = it0.next();
            QuantifiableVariable key = en.key();
            Term value = en.value();
            if (map1.containsKey(key)) {
                if (!(map1.get(key).equals(value)))
                    return null;
            }
            resMap = resMap.put(key, value);
        }
        IteratorOfEntryOfQuantifiableVariableAndTerm it1 = map1.entryIterator();
        while (it1.hasNext()) {
            EntryOfQuantifiableVariableAndTerm en = it1.next();
            resMap = resMap.put(en.key(), en.value());
        }
        
        return new Substitution(resMap);
    }
    

    
    public boolean equals(Object arg0) {
        if (!(arg0 instanceof MultiTrigger)) return false;

        final MultiTrigger a = (MultiTrigger) arg0;
        return a.triggers.equals(triggers);
    }
    public int hashCode() {
        return triggers.hashCode();
    }
    public String toString() {
        return "" + triggers;
    }

    public Term getTriggerTerm() {
	return clause;
    }

}
     
