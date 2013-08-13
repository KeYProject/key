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

package org.key_project.key4eclipse.common.ui.starter;

import org.eclipse.jdt.core.IMethod;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Instances of this class are used to start an application
 * and to load the given existing {@link Proof} in it.
 * @author Martin Hentschel
 */
public interface IProofStarter {
   /**
    * Open the application.
    * @param proof The {@link Proof} to load.
    * @param environment The {@link KeYEnvironment} in which the {@link Proof} lives.
    * @param method An optional {@link IMethod} from which the {@link Proof} was started.
    * @param canStartAutomode {@code true} can start auto mode, {@code false} is not allowed to start auto mode.
    * @param canApplyRules {@code true} can apply rules, {@code false} is not allowed to apply rules.
    * @param canPruneProof {@code true} can prune proof, {@code false} is not allowed to prune proof.
    * @param canStartSMTSolver {@code true} can start SMT solver, {@code false} is not allowed to start SMT solver.
    * @throws Exception Occurred Exception.
    */
   public void open(Proof proof, 
                    KeYEnvironment<CustomConsoleUserInterface> environment, 
                    IMethod method,
                    boolean canStartAutomode,
                    boolean canApplyRules,
                    boolean canPruneProof,
                    boolean canStartSMTSolver) throws Exception;
}