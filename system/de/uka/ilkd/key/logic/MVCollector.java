// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.op.Metavariable;
/** This class is used to collect all appearing metavariables in a
 * term. Duplicates are not removed becaues the use of persistent
 * datastructure and up to now we just have a SetAsList-implementaion
 * causing to have O(sqr(n)) if it would used.
*/

public class MVCollector extends Visitor{
    /** collects all found Metavraibles */
    private ImmutableList<Metavariable> mvList;

    /** creates the metavariable collector */
    public MVCollector() {
	mvList=ImmutableSLList.<Metavariable>nil();
    }

    /** is called by the execPostOrder-method of a term 
     * @param t the Term to checked if it is a Metavariable and if true the
     * Metavariable is added to the list of found Metavariables
     */  
    public void visit(Term t) {
	if (t.op() instanceof Metavariable) {
	    mvList=mvList.prepend((Metavariable)t.op());
	}
    }

    /** @return iterator of the found metavariables */
    public Iterator<Metavariable> mv() {
	return mvList.iterator();
    }
}
