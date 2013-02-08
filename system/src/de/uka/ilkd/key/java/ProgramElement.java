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



package de.uka.ilkd.key.java;

import de.uka.ilkd.key.rule.MatchConditions;

/**
 *    A part of the program syntax that carries semantics in the model.
 * taken from COMPOST and changed to achieve an immutable structure
 */
public interface ProgramElement extends SourceElement, ModelElement {


    /**
     *Get comments.
     *@return the comments.
     */
    Comment[] getComments();


       
    /**
     * matches the source "text" (@link SourceData#getSource()) against the pattern represented 
     * by this object. In case of a successful match the resulting {@link MatchConditions} with 
     * the found instantiations of the schemavariables. If the match 
     * failed, <tt>null</tt> is returned instead. 
     * 
     * @param source the SourceData with the program element to match
     * @param matchCond the MatchConditions found up to this point
     * @return the resulting match conditions or <tt>null</tt> if the match failed 
     */
    MatchConditions match(SourceData source, MatchConditions matchCond);

}
