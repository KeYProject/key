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
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.rule.RuleSet;



public class RuleSetModelInfo extends AbstractTacletContainer {
    private RuleSet ruleSet;
    private String definition;
    private boolean isVirtual;
    private ListOfRuleSetModelInfo intersectingSets = SLListOfRuleSetModelInfo.EMPTY_LIST;
    private ListOfRuleSetModelInfo superSets = SLListOfRuleSetModelInfo.EMPTY_LIST;
    private ListOfRuleSetModelInfo subSets = SLListOfRuleSetModelInfo.EMPTY_LIST;
    private ListOfRuleSetModelInfo equalSets = SLListOfRuleSetModelInfo.EMPTY_LIST;
    
    public RuleSetModelInfo ( RuleSet ruleSet ) {
        this.ruleSet = ruleSet;
        this.definition = null;
        this.isVirtual = false;
    }
    
    public RuleSetModelInfo ( RuleSet ruleSet, String definition, boolean isVirtual ) {
    	this.ruleSet = ruleSet;
    	this.definition = definition;
    	this.isVirtual = isVirtual;
    }
    
    public RuleSet getRuleSet () {
        return ruleSet;
    }
    
    public ListOfRuleSetModelInfo getSuperSets () {
        return superSets;
    }
    
    public void setSuperSets ( ListOfRuleSetModelInfo superSets ) {
        this.superSets = superSets;
    }
    
    public void addSuperSet ( RuleSetModelInfo set ) {
        superSets = superSets.prepend ( set );
    }
    
    public ListOfRuleSetModelInfo getEqualSets () {
        return equalSets;
    }
    
    public void setEqualSets ( ListOfRuleSetModelInfo equalRuleSets ) {
        this.equalSets = equalRuleSets;
    }
    
    public void addEqualSet ( RuleSetModelInfo set ) {
        equalSets = equalSets.prepend ( set );
    }
    
    public ListOfRuleSetModelInfo getIntersectingSets () {
        return intersectingSets;
    }
    
    public void setIntersectingSets ( ListOfRuleSetModelInfo intersectingRuleSets ) {
        this.intersectingSets = intersectingRuleSets;
    }
    
    public void addIntersectingSet ( RuleSetModelInfo set ) {
        intersectingSets = intersectingSets.prepend ( set );
    }
    
    public ListOfRuleSetModelInfo getSubSets () {
        return subSets;
    }
    
    public void setSubSets ( ListOfRuleSetModelInfo subSets ) {
        this.subSets = subSets;
    }
    
    public void addSubSet ( RuleSetModelInfo set ) {
        subSets = subSets.prepend ( set );
    }
    
    public Name name () {
        return ruleSet.name();
    }
    
    public boolean isVirtual () {
    	return isVirtual;
    }
    
    public String getDefinition() {
    	return definition;
    }
}
