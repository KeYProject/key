/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

import org.eclipse.core.resources.IProject;
import org.key_project.key4eclipse.starter.core.util.event.IProofProviderListener;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;

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
    * The optional {@link UserInterfaceControl} in which all of {@link #getCurrentProofs()} lives.
    * @return The {@link UserInterfaceControl} in which all of {@link #getCurrentProofs()} lives or {@code null} if not available.
    */
   public UserInterfaceControl getUI();
   
   /**
    * Return the {@link ProofControl} of {@link #getUI()}.
    * @return The {@link ProofControl} of {@link #getUI()}.
    */
   public ProofControl getProofControl();
   
   /**
    * The optional {@link KeYEnvironment} in which all of {@link #getCurrentProofs()} lives.
    * @return The {@link KeYEnvironment} in which all of {@link #getCurrentProofs()} lives or {@code null} if not available.
    */
   public KeYEnvironment<?> getEnvironment();
   
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
   
   /**
    * Returns the project which provides the proof or the source code.
    * @return The {@link IProject} if known or {@code null} if unknown.
    */
   public IProject getProject();

   /**
    * Checks if it is allowed to start the auto mode.
    * @return {@code true} can start auto mode, {@code false} is not allowed to start auto mode.
    */
   public boolean isCanStartAutomode();
   
   /**
    * Checks if it is allowed to apply rules.
    * @return {@code true} can apply rules, {@code false} is not allowed to apply rules.
    */
   public boolean isCanApplyRules();

   /**
    * Checks if it is allowed to prune proof.
    * @return {@code true} can prune proof, {@code false} is not allowed to prune proof.
    */
   public boolean isCanPruneProof();

   /**
    * Checks if it is allowed to start SMT solver.
    * @return {@code true} can start SMT solver, {@code false} is not allowed to start SMT solver.
    */
   public boolean isCanStartSMTSolver();
}