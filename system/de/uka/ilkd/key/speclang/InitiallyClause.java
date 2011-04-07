// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


public interface InitiallyClause extends SpecificationElement {
     

    
    
    /**
     * Returns the formula without implicit all-quantification over
     * the receiver object.
     */
    public Term getClause(ParsableVariable selfVar, Services services);
    
    public InitiallyClause setKJT(KeYJavaType newKjt);

    /**
     * Translate this initially clause to a contract for the given constructor.
     * Exception is thrown if the methods passed is not a constructor.
     * For an initially clause <tt>inic</tt> the resulting contract looks like:<br>
     * <tt>requires true;<br>ensures inic;<br>signals (Exception) inic;<br>diverges true;</tt>
     * @param pm constructor
     * @throws SLTranslationException 
     */
    public ImmutableSet<Contract> toContract(ProgramMethod pm) ;
  
}
