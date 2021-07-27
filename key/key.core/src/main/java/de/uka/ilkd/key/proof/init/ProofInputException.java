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
package de.uka.ilkd.key.proof.init;

import org.antlr.runtime.RecognitionException;

/**
 * Reading prover input failed
 */
public class ProofInputException extends RecognitionException {
    private static final long serialVersionUID = 1028674319098864943L;
    private final String message;

   public ProofInputException(Exception e) {
      this(e.getMessage(), e);
   }

   public ProofInputException(String s) {
      this(s, null);
   }

   public ProofInputException(String message, Throwable cause) {
      this.message = message;
      if(cause != null) {
    	  initCause(cause);
      }
   }

   @Override
   public String getMessage() {
      return message;
   }

}
