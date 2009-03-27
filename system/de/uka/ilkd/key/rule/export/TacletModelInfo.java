// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design 
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                      and Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License.
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.export;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.rule.Taclet;



public class TacletModelInfo implements Named {
    private Taclet taclet;
    private String filename;
    private TacletModelInfo introducingTaclet = null;
    private DisplayNameModelInfo displayName;
    private ListOfOptionModelInfo options = SLListOfOptionModelInfo.EMPTY_LIST;
    private ListOfRuleSetModelInfo ruleSets = SLListOfRuleSetModelInfo.EMPTY_LIST;

    public TacletModelInfo ( Taclet taclet, String filename ) {
        this.taclet = taclet;
        this.filename = filename;
    }
    
    /**
     * @return Returns the filename.
     */
    public String getFilename () {
        return filename;
    }
    
    /**
     * @return Returns the taclet.
     */
    public Taclet getTaclet () {
        return taclet;
    }
    
    /**
     * @return Returns the introducingTaclet.
     */
    public TacletModelInfo getIntroducingTaclet () {
        return introducingTaclet;
    }
    
    /**
     * @param introducingTaclet The introducingTaclet to set.
     */
    public void setIntroducingTaclet ( TacletModelInfo introducingTaclet ) {
        this.introducingTaclet = introducingTaclet;
    }
    
    public Name name () {
        return taclet.name();
    }
    
    /**
     * @return Returns the displayName.
     */
    public DisplayNameModelInfo getDisplayName () {
        return displayName;
    }
    
    /**
     * @param displayName The displayName to set.
     */
    public void setDisplayName ( DisplayNameModelInfo displayName ) {
        this.displayName = displayName;
    }
    
    /**
     * @return Returns the options.
     */
    public ListOfOptionModelInfo getOptions () {
        return options;
    }
    
    /**
     * @param options The options to set.
     */
    public void setOptions ( ListOfOptionModelInfo options ) {
        this.options = options;
    }
    
    public void addOption ( OptionModelInfo opt ) {
        if ( !options.contains(opt)) {
            options = options.prepend(opt);
        }
    }
    /**
     * @return Returns the ruleSets.
     */
    public ListOfRuleSetModelInfo getRuleSets () {
        return ruleSets;
    }
    
    /**
     * @param ruleSets The ruleSets to set.
     */
    public void setRuleSets ( ListOfRuleSetModelInfo ruleSets ) {
        this.ruleSets = ruleSets;
    }
    
    public void addRuleSet ( RuleSetModelInfo ruleSet ) {
        if ( !ruleSets.contains(ruleSet) ) {
            ruleSets = ruleSets.prepend ( ruleSet );
        }
    }
}
