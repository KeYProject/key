// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.rule.tacletbuilder;

import java.util.Iterator;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.NotFreeIn;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletPrefix;
import de.uka.ilkd.key.rule.TacletSchemaVariableCollector;

public class TacletPrefixBuilder {

    /** 
     * set of all schemavariables that are only allowed to be matched
     * with quantifiable variables. 
     */
    private ImmutableSet<SchemaVariable> currentlyBoundVars = DefaultImmutableSet.<SchemaVariable>nil();
    private TacletBuilder tacletBuilder;

    protected ImmutableMap<SchemaVariable,TacletPrefix> prefixMap = DefaultImmutableMap.<SchemaVariable,TacletPrefix>nilMap();

    TacletPrefixBuilder(TacletBuilder tacletBuilder) {
	this.tacletBuilder=tacletBuilder;
    }

    private void addVarsBoundHere(Term visited, int subTerm) {
	ImmutableArray<QuantifiableVariable> bdVars=visited.varsBoundHere(subTerm);
	for (int i=0; i<bdVars.size(); i++) {
	    QuantifiableVariable boundVar = bdVars.get(i);
	    if ( boundVar instanceof VariableSV ) {
		currentlyBoundVars = currentlyBoundVars.add
		    ((SchemaVariable)boundVar);
	    }
	}
    }

    private void setPrefixOfOccurrence(SchemaVariable sv, 
				       ImmutableSet<SchemaVariable> relevantBoundVars) {
	prefixMap = 
	    prefixMap.put(sv, new TacletPrefix(relevantBoundVars, false));
    }

    /**
     * removes all variables x that are declared as x not free in sv from the
     * currently bound vars set.
     */
    private ImmutableSet<SchemaVariable> removeNotFreeIn(SchemaVariable sv) {
	ImmutableSet<SchemaVariable> result = currentlyBoundVars;
	Iterator<NotFreeIn> it = tacletBuilder.varsNotFreeIn();
	while (it.hasNext()) {
	    NotFreeIn notFreeIn=it.next();
	    if (notFreeIn.second() == sv) {
		result = result.remove(notFreeIn.first());
	    }
	}
	return result;
    }

    private void visit(Term t) {
	if (t.op() instanceof SchemaVariable && 
            t.arity() == 0 &&
	    !(t.op() instanceof VariableSV) &&
	    !(t.op() instanceof ProgramSV) &&
	    !(t.op() instanceof SkolemTermSV)) {
	    SchemaVariable sv = (SchemaVariable)t.op();
	    ImmutableSet<SchemaVariable> relevantBoundVars = removeNotFreeIn(sv);
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
	    ImmutableSet<SchemaVariable> oldBounds=currentlyBoundVars;
	    addVarsBoundHere(t, i);
	    visit(t.sub(i));
	    currentlyBoundVars=oldBounds;
	}
	if (t.hasLabels()) {
	    for (TermLabel l: t.getLabels()) {
	        if (l instanceof SchemaVariable) {
	            SchemaVariable sv = (SchemaVariable)l;
	            ImmutableSet<SchemaVariable> relevantBoundVars = removeNotFreeIn(sv);
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
	    }
	}
    }
    

    private void visit(Sequent s) {
        for (final SequentFormula cf : s) {
            visit(cf.formula());
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

	Iterator<TacletGoalTemplate> itGoalTempl
	    = tacletBuilder.goalTemplates().iterator();

	while (itGoalTempl.hasNext()) {
	    visit(itGoalTempl.next());
	}
	
	itGoalTempl = tacletBuilder.goalTemplates().iterator();
	while (itGoalTempl.hasNext()) {
	    final Iterator<Taclet> addRules = itGoalTempl.next().rules().iterator();
	    while (addRules.hasNext()) {
		checkPrefixInAddRules(addRules.next());
	    }
	}
    }


    private void checkPrefixInAddRules(Taclet addRule) {
	final ImmutableMap<SchemaVariable,TacletPrefix> addRuleSV2PrefixMap = 
	    addRule.prefixMap();
	final Iterator<ImmutableMapEntry<SchemaVariable,TacletPrefix>> it = 
	    prefixMap.entryIterator();
	while (it.hasNext()) {
	    final ImmutableMapEntry<SchemaVariable,TacletPrefix> entry = it.next();
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

        for (TacletGoalTemplate tacletGoalTemplate : addRule.goalTemplates()) {
            for (Taclet taclet : tacletGoalTemplate.rules()) {
                checkPrefixInAddRules(taclet);
            }
        }
    }
    

    private boolean atMostOneRepl() {
	RewriteTacletBuilder rwtacletBuilder=(RewriteTacletBuilder)tacletBuilder;
	Iterator<TacletGoalTemplate> it
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
        for (TacletGoalTemplate tacletGoalTemplate : rwtacletBuilder.goalTemplates()) {
            TacletGoalTemplate tmpl = tacletGoalTemplate;
//	    if (tmpl instanceof RewriteTacletGoalTemplate) {	    
//		RewriteTacletGoalTemplate
//		    gt=(RewriteTacletGoalTemplate)tmpl; 
            svc.visit(tmpl.sequent());
            for (Taclet taclet : tmpl.rules()) { // addrules
                svc.visit(taclet, true);
            }
        }
        //	    }	
	return !svc.contains(sv);
    }

    private void considerContext() {
	if (!(tacletBuilder instanceof RewriteTacletBuilder) || !atMostOneRepl()) {
	    return;
	}
	Iterator<ImmutableMapEntry<SchemaVariable,TacletPrefix>> it = prefixMap.entryIterator();
	while (it.hasNext()) {
	    ImmutableMapEntry<SchemaVariable,TacletPrefix> entry = it.next();
	    if (occurrsOnlyInFindOrRepl(entry.key())) {
		prefixMap = prefixMap.put(entry.key(), 
					  entry.value().setContext(true));
	    }
	}
    }

    public ImmutableMap<SchemaVariable,TacletPrefix> getPrefixMap() { 
	considerContext();
	return prefixMap;
    }
    
    public static class InvalidPrefixException extends IllegalStateException {
        private static final long serialVersionUID = 5855187579027274363L;
        
        InvalidPrefixException(String tacletName, 
                SchemaVariable sv,
                TacletPrefix prefix,
                ImmutableSet<SchemaVariable> sndPrefixVar) {
            super("Schema variable " + sv + "occurs at different places " + 
                    "in taclet " + tacletName + " with different prefixes.\n" +
                    "Prefix P1:"+((prefix == null) ? DefaultImmutableSet.<SchemaVariable>nil() : prefix.prefix()) +
                    "\n" +
                    "Prefix P2:"+ sndPrefixVar);
        }

    }

}


