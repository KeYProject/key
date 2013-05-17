/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.keyide.ui.editor;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * An interface to provide fundamental functions for accessing the {@link KeYEnvironment}.
 * @author Martin Hentschel
 */
public interface IProofEnvironmentProvider {
   
   /**
    * The {@link KeYEnvironment} for this {@link KeYEditor}.
    * @return The {@link KeYEnvironment} for this {@link KeYEditor}.
    */
   public KeYEnvironment<CustomConsoleUserInterface> getKeYEnvironment();

   /**
    * The {@link Proof} for this {@link KeYEditor}.
    * @return The {@link Proof} for this {@link KeYEditor}.
    */
   public Proof getProof();
}