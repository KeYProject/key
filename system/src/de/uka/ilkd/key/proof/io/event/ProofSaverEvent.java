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

package de.uka.ilkd.key.proof.io.event;

import java.util.EventObject;

import de.uka.ilkd.key.proof.io.ProofSaver;

/**
 * An event thrown by a {@link ProofSaver}.
 * @author Martin Hentschel
 */
public class ProofSaverEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 6000441441638546982L;

   /**
    * The file name.
    */
   private final String filename;
   
   /**
    * The error message.
    */
   private final String errorMsg;
   
   /**
    * Constructor.
    * @param source The {@link ProofSaver} which throws this event.
    * @param filename The file name.
    * @param errorMsg The error message.
    */
   public ProofSaverEvent(ProofSaver source, String filename, String errorMsg) {
      super(source);
      this.filename = filename;
      this.errorMsg = errorMsg;
   }

   /**
    * Returns the file name.
    * @return The file name.
    */
   public String getFilename() {
      return filename;
   }

   /**
    * Returns the error message.
    * @return The error message.
    */
   public String getErrorMsg() {
      return errorMsg;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ProofSaver getSource() {
      return (ProofSaver)super.getSource();
   }
}