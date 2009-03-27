// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//This file is part of KeY - Integrated Deductive Software Design 
//Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//and Chalmers University of Technology, Sweden          
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.SourceElement;

/** represents the logical name for an attribute with the containing
 * class as an additional string
 */

public class AttributeElementName extends ProgramElementName {
	
	protected String containerString;
	
	/** create a new name
	 * @param name the name
	 */
	public AttributeElementName(String name, String container){
		super(name);
		containerString = container;
	}
	
	public void prettyPrint(PrettyPrinter w) throws java.io.IOException {
		w.printProgramElementName(this);
	}
	
	
	
	/** equals modulo renaming is described in the corresponding
	 * comment in class SourceElement. The ProgramElementName has to
	 * check if an abstract name has been assigned and if, if both
	 * elements are assigned to the same name, otherwise the names
	 * have to be equal
	 */
	public boolean equalsModRenaming(SourceElement se, 
			NameAbstractionTable nat) {
		if (!(se instanceof AttributeElementName)) {
			return false;
		}
		return nat.sameAbstractName(this, se);
	}
}

