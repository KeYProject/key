// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.Reference;
import de.uka.ilkd.key.logic.op.IProgramMethod;

/**
 * extracted interface to allow schema variabes to stand for an
 * execution context
 */
public interface IExecutionContext extends Reference {
   /**
    * returns the type reference to the next enclosing class
    * @return the type reference to the next enclosing class
    */
   public TypeReference getTypeReference();
   
   /**
    * returns the program method which is currently active
    * @return the currently active method
    */
   public IProgramMethod getMethodContext();
   
   /**
    * returns the runtime instance object
    * @return the runtime instance object
    */
   public ReferencePrefix getRuntimeInstance();
}