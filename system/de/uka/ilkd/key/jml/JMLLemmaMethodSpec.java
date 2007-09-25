// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.jml;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.mgt.ListOfQuantifierPrefixEntry;


/** Methodspecs which implement this interface can be used for generating 
 * lemmas.
 */
public interface JMLLemmaMethodSpec{

    /** returns precondition with represents relations applied */
    Term getCompletePre(boolean withClassSpec, boolean allInv, 
			boolean terminationCase);

    /** returns the variables used for the specification of <code>\old<\code>*/
    ListOfQuantifierPrefixEntry getOldLVs();

    /** returns the "<code>\old<\code>-equations"*/
    Term getPi1();

    /** returns postcondition with represents relations applied */
    Term getCompletePost(boolean withClassSpec, boolean allInv);

    /** returns the modifies clause*/
    SetOfLocationDescriptor replaceModelFieldsInAssignable();

    /** returns the ProgramElement used in the findpart of the lemmataclet*/
    ProgramElement getProofStatement();

    /** returns true iff the specification demands termination (normally or by
     * throwing an exception). 
     */
    boolean terminates();

    /** returns true if this specification is prevented from being used for 
     * generating a lemma rule for any reason.
     */
//    boolean otherObstacles();

}
