// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.IteratorOfConstrainedFormula;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;

public class TacletPrefixBuilder {

    /** 
     * set of all schemavariables that are only allowed to be matched
     * with quantifiable variables. 
     */
    private SetOfSchemaVariable currentlyBoundVars = SetAsListOfSchemaVariable.EMPTY_SET;
    private TacletBuilder tacletBuilder;

    protected MapFromSchemaVariableToTacletPrefix prefixMap = MapAsListFromSchemaVariableToTacletPrefix.EMPTY_MAP;

    TacletPrefixBuilder(TacletBuilder tacletBuilder) {
	this.tacletBuilder=tacletBuilder;
    }

    private void addVarsBoundHere(Term visited, int subTerm) {
	ArrayOfQuantifiableVariable bdVars=visited.varsBoundHere(subTerm);
	for (int i=0; i<bdVars.size(); i++) {
	    QuantifiableVariable boundVar = bdVars.getQuantifiableVariable(i);
	    if ( boundVar instanceof SchemaVariable &&
		 ((SchemaVariable)boundVar).isVariableSV() ) {
		currentlyBoundVars = currentlyBoundVars.add
		    ((SchemaVariable)boundVar);
	    }
	}
    }

    private void setPrefixOfOccurrence(SchemaVariable sv, 
				       SetOfSchemaVariable relevantBoundVars) {
	prefixMap = 
	    prefixMap.put(sv, new TacletPrefix(relevantBoundVars, false));
    }

    /**
     * removes all variables x that are declared as x not free in sv from the
     * currently bound vars set.
     */
    private SetOfSchemaVariable removeNotFreeIn(SchemaVariable sv) {
	SetOfSchemaVariable result = currentlyBoundVars;
	IteratorOfNotFreeIn it = tacletBuilder.varsNotFreeIn();
	while (it.hasNext()) {
	    NotFreeIn notFreeIn=it.next();
	    if (notFreeIn.second() == sv) {
		result = result.remove(notFreeIn.first());
	    }
	}
	return result;
    }

    private void visit(Term t) {
	if (t.op() instanceof SortedSchemaVariable && 
	    !((SchemaVariable)t.op()).isVariableSV() &&
	    !((SchemaVariable)t.op()).isProgramSV() &&
	    !((SchemaVariable)t.op()).isSkolemTermSV()) {    // see below /AR
	    SchemaVariable sv = (SchemaVariable)t.op();
	    SetOfSchemaVariable relevantBoundVars = removeNotFreeIn(sv);
	    TacletPrefix prefix = prefixMap.get(sv);
	    if (prefix == null || prefix.prefix().equals(relevantBoundVars)) {
		setPrefixOfOccurrence(sv, relevantBoundVars);
	    } else {
		throw new InvalidPrefixException(tacletBuilder.getName().toString(), 
						 sv, 
						 prefix, 
						 relevantBoundVars);
	    }
	} 
	for (int i=0; i<t.arity(); i++) {
	    SetOfSchemaVariable oldBounds=currentlyBoundVars;
	    addVarsBoundHere(t, i);
	    visit(t.sub(i));
	    currentlyBoundVars=oldBounds;
	}
    }
    

    private void visit(Sequent s) {
	IteratorOfConstrainedFormula it=s.iterator();
	while (it.hasNext()) {
	    visit(it.next().formula());
	}
    }

    private void visit(TacletGoalTemplate templ) {
	visit(templ.sequent());
	if (templ instanceof RewriteTacletGoalTemplate) {
	    visit(((RewriteTacletGoalTemplate)templ).replaceWith());
	}
	if (templ instanceof AntecSuccTacletGoalTemplate) {
	    visit(((AntecSuccTacletGoalTemplate)templ).replaceWith());
	}
    }

    public void build() {
	visit(tacletBuilder.ifSequent());

	if (tacletBuilder instanceof FindTacletBuilder) {
	    visit(((FindTacletBuilder)tacletBuilder).getFind());
	}

	IteratorOfTacletGoalTemplate itGoalTempl
	    = tacletBuilder.goalTemplates().iterator();

	while (itGoalTempl.hasNext()) {
	    visit(itGoalTempl.next());
	}
	
	itGoalTempl = tacletBuilder.goalTemplates().iterator();
	while (itGoalTempl.hasNext()) {
	    final IteratorOfTaclet addRules = itGoalTempl.next().rules().iterator();
	    while (addRules.hasNext()) {
		checkPrefixInAddRules(addRules.next());
	    }
	}
    }


    private void checkPrefixInAddRules(Taclet addRule) {
	final MapFromSchemaVariableToTacletPrefix addRuleSV2PrefixMap = 
	    addRule.prefixMap();
	final IteratorOfEntryOfSchemaVariableAndTacletPrefix it = 
	    prefixMap.entryIterator();
	while (it.hasNext()) {
	    final EntryOfSchemaVariableAndTacletPrefix entry = it.next();
	    final TacletPrefix addRulePrefix = addRuleSV2PrefixMap.get(entry.key());
	    
	    if (addRulePrefix != null && !addRulePrefix.prefix().
	            equals(entry.value().prefix())) {
		throw new InvalidPrefixException(tacletBuilder.getName().toString(), 
						 entry.key(), 
						 entry.value(),
						 addRulePrefix.prefix());	    
	    }
	}

	// we have to descend into the addrules of the addrules

	final IteratorOfTacletGoalTemplate templateIt = addRule.goalTemplates().iterator();
	while (templateIt.hasNext()) {
	    final IteratorOfTaclet moreRules = templateIt.next().rules().iterator();
	    while (moreRules.hasNext()) {
		checkPrefixInAddRules(moreRules.next());
	    }
	}	
    }
    

    private boolean atMostOneRepl() {
	RewriteTacletBuilder rwtacletBuilder=(RewriteTacletBuilder)tacletBuilder;
	IteratorOfTacletGoalTemplate it
	    =rwtacletBuilder.goalTemplates().iterator();
	int count=0;
	while (it.hasNext()) {
	    TacletGoalTemplate tmpl = it.next();
	    if (tmpl instanceof RewriteTacletGoalTemplate) {
		if (((RewriteTacletGoalTemplate)tmpl).replaceWith()!=null) {
		    count++;
		}
	    }
	    if (count>1) return false;
	}
	return true;
    }

    private boolean occurrsOnlyInFindOrRepl(SchemaVariable sv) {
	RewriteTacletBuilder rwtacletBuilder=(RewriteTacletBuilder)tacletBuilder;
	TacletSchemaVariableCollector svc=new TacletSchemaVariableCollector();
	svc.visit(rwtacletBuilder.ifSequent());
	IteratorOfTacletGoalTemplate it
	    = rwtacletBuilder.goalTemplates().iterator();
	while (it.hasNext()) {
	    TacletGoalTemplate tmpl = it.next();
//	    if (tmpl instanceof RewriteTacletGoalTemplate) {	    
//		RewriteTacletGoalTemplate
//		    gt=(RewriteTacletGoalTemplate)tmpl; 
		svc.visit(tmpl.sequent());   
		IteratorOfTaclet addRuleIt = tmpl.rules().iterator();
		while (addRuleIt.hasNext()) { // addrules
		    svc.visit(addRuleIt.next(), true);
		}
        }
        //	    }	
	return !svc.contains(sv);
    }

    private void considerContext() {
	if (!(tacletBuilder instanceof RewriteTacletBuilder) || !atMostOneRepl()) {
	    return;
	}
	IteratorOfEntryOfSchemaVariableAndTacletPrefix it = prefixMap.entryIterator();
	while (it.hasNext()) {
	    EntryOfSchemaVariableAndTacletPrefix entry = it.next();
	    if (occurrsOnlyInFindOrRepl(entry.key())) {
		prefixMap = prefixMap.put(entry.key(), 
					  entry.value().setContext(true));
	    }
	}
    }

    public MapFromSchemaVariableToTacletPrefix getPrefixMap() { 
	considerContext();
	return prefixMap;
    }
    
    class InvalidPrefixException extends IllegalStateException {
        /**
         * 
         */
        private static final long serialVersionUID = 5855187579027274363L;
        
        InvalidPrefixException(String tacletName, 
                SchemaVariable sv,
                TacletPrefix prefix,
                SetOfSchemaVariable sndPrefixVar) {
            super("Schema variable " + sv + "occurs at different places " + 
                    "in taclet " + tacletName + " with different prefixes.\n" +
                    "Prefix P1:"+((prefix == null) ? SetAsListOfSchemaVariable.EMPTY_SET : prefix.prefix()) +
                    "\n" +
                    "Prefix P2:"+ sndPrefixVar);
        }

    }

}


