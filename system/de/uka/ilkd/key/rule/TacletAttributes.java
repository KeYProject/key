// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/** class contains optional attributes of a Taclet. 
 */

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.ListOfName;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.SLListOfName;

public class TacletAttributes {
    private boolean noninteractive;
   
    private String displayName;
    private ListOfName oldNames;
    private String helpText;


   public TacletAttributes() {
	this.noninteractive = false;	
        this.displayName = null;
        this.oldNames = SLListOfName.EMPTY_LIST;
        this.helpText = null;
   }

    
    /** returns true if the <I>interactive</I> option is set */
    public boolean noninteractive() {
	return noninteractive;
    }

    
    public String displayName() {
       return displayName;
    }
    
    public ListOfName oldNames() {
       return oldNames;
    }
    
    public String helpText() {
       return helpText;
    }
    

    /** sets an optional display name (presented to the user)
     */
    public void setDisplayName(String s) {
       displayName = s;
    }

    /** adds an old name to the list of old names
     */
    public void addOldName(String s) {
        oldNames = oldNames.prepend(new Name(s));
    }


    public void setHelpText(String s) {
       helpText = s;
    }

    /** sets the noninteractive flag to the given value.
     */
    public void setNoninteractive(boolean ni) {
	noninteractive = ni;
    }
    
    
    
}
