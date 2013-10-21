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

package org.key_project.key4eclipse.starter.core.util;

import org.key_project.key4eclipse.starter.core.util.event.IProofProviderListener;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * Implementations of this class does something with one {@link Proof}
 * at a time and allows other to access it.
 * @author Martin Hentschel
 */
public interface IProofProvider {
   /**
    * Returns the currently active (edited) {@link Proof}, e.g. the first one of {@link #getCurrentProofs()}.
    * @return The currently active (edited) {@link Proof}, e.g. the first one of {@link #getCurrentProofs()}.
    */
   public Proof getCurrentProof();
   
   /**
    * Returns all currently active (edited) provided {@link Proof}s.
    * @return All currently active (edited)  provided {@link Proof}s.
    */
   public Proof[] getCurrentProofs();
   
   /**
    * The optional {@link UserInterface} in which all of {@link #getCurrentProofs()} lives.
    * @return The {@link UserInterface} in which all of {@link #getCurrentProofs()} lives or {@code null} if not available.
    */
   public UserInterface getUI();
   
   /**
    * The optional {@link KeYEnvironment} in which all of {@link #getCurrentProofs()} lives.
    * @return The {@link KeYEnvironment} in which all of {@link #getCurrentProofs()} lives or {@code null} if not available.
    */
   public KeYEnvironment<?> getEnvironment();
   
   /**
    * Returns the used {@link KeYMediator}.
    * @return The used {@link KeYMediator}.
    */
   public KeYMediator getMediator();
   
   /**
    * Adds the given {@link IProofProviderListener}.
    * @param l The {@link IProofProviderListener} to add.
    */
   public void addProofProviderListener(IProofProviderListener l);

   /**
    * Removes the given {@link IProofProviderListener}.
    * @param l The {@link IProofProviderListener} to remove.
    */
   public void removeProofProviderListener(IProofProviderListener l);
}