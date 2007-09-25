//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ParsableVariable;


public interface ClassInvariant {
  public ModelClass getModelClass();

  public KeYJavaType getKJT(Services services);

  public FormulaWithAxioms getInv(Services services) throws SLTranslationError;
  
  public FormulaWithAxioms getOpenInv(ParsableVariable selfVar, 
	      			      Services services) throws SLTranslationError;
}
