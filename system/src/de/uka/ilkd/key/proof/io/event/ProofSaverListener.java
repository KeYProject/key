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

import java.util.EventListener;

import de.uka.ilkd.key.proof.io.ProofSaver;

/**
 * Listens for changes on {@link ProofSaver} instances.
 * @author Martin Hentschel
 */
public interface ProofSaverListener extends EventListener {
   /**
    * This method is called when a file was saved via {@link ProofSaver#save()}.
    * @param e The {@link ProofSaverEvent}.
    */
   public void proofSaved(ProofSaverEvent e);
}