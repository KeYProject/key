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


/** class contains optional attributes of a Taclet. 
 */

package de.uka.ilkd.key.rule;



public final class TacletAttributes {
   
    private String displayName;
    private String helpText;
    
    /** trigger related information */
    private Trigger trigger;



   public TacletAttributes() {
        this.displayName = null;
        this.helpText = null;
   }

    
    public String displayName() {
       return displayName;
    }
    
    public String helpText() {
       return helpText;
    }

    /** sets an optional display name (presented to the user)
     */
    public void setDisplayName(String s) {
       displayName = s;
    }

    public void setHelpText(String s) {
       helpText = s;
    }


    public Trigger getTrigger() {
        return trigger;
    }


    public void setTrigger(Trigger trigger) {
        this.trigger = trigger;
    }


}
