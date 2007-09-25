// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.casetool.IteratorOfModelClass;
import de.uka.ilkd.key.casetool.ListOfModelClass;
import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.util.Debug;


/**
 * A dialog for selecting one of a class's superclasses.
 */
public class SuperclassSelectionDialog extends ClassSelectionDialog {
    
    private static ListOfModelClass getAllSuperclasses(ModelClass subtype) {
        ListOfModelClass result = subtype.getMyParents();
        
        IteratorOfModelClass it = result.iterator(); 
        while(it.hasNext()) {
            result = result.append(getAllSuperclasses(it.next()));
        }
        
        return result; //TODO: eliminate duplicates
    }
    
    
    /**
     * Creates and displays a dialog box asking the user to select a superclass.
     * @param subclass the class to choose a superclass of
     */
    public SuperclassSelectionDialog(ModelClass subclass) {
    	super("Please select a supertype", 
              "Supertypes of " + subclass.getClassName(),
              getAllSuperclasses(subclass),
              false);
    }
    
   
    /**
     * Returns the selected supertype, or null.
     */
    public ModelClass getSuperclass() {
        ListOfModelClass selectedClasses = getSelection();
        Debug.assertTrue(selectedClasses.size() <= 1);
        return (selectedClasses.isEmpty() ? null : selectedClasses.head());
    }
}
