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

package org.key_project.keyide.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.key_project.keyide.ui.editor.KeYEditor;

/**
 * This property tester can be used to check if a {@link KeYEditor} provides
 * a function. It supports:
 * <ul>
 *    <li>{@link KeYEditor#isCanStartAutomode()}</li>
 *    <li>{@link KeYEditor#isCanApplyRules()}</li>
 *    <li>{@link KeYEditor#isCanPruneProof()}</li>
 *    <li>{@link KeYEditor#isCanStartSMTSolver()}</li>
 * </ul>
 * @author Martin Hentschel
 */
public class CanFunctionPropertyTester extends PropertyTester {
   /**
    * Property to test {@link KeYEditor#isCanStartAutomode()}
    */
   public static final String CAN_START_AUTO_MODE = "canStartAutomode";

   /**
    * Property to test {@link KeYEditor#isCanApplyRules()} 
    */
   public static final String CAN_APPLY_RULES = "canApplyRules";

   /**
    * Property to test {@link KeYEditor#isCanPruneProof()}
    */
   public static final String CAN_PRUNE_PROOF = "canPruneProof";

   /**
    * Property to test {@link KeYEditor#isCanStartSMTSolver()}
    */
   public static final String CAN_START_SMT_SOLVER = "canStartSMTSolver";

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, 
                       String property, 
                       Object[] args, 
                       Object expectedValue) {
      if (receiver instanceof KeYEditor) {
         KeYEditor editor = (KeYEditor)receiver;
         if (CAN_START_AUTO_MODE.equals(property)) {
            return editor.isCanStartAutomode();
         }
         else if (CAN_APPLY_RULES.equals(property)) {
            return editor.isCanApplyRules();
         }
         else if (CAN_PRUNE_PROOF.equals(property)) {
            return editor.isCanPruneProof();
         }
         else if (CAN_START_SMT_SOLVER.equals(property)) {
            return editor.isCanStartSMTSolver();
         }
         else {
            return false;
         }
      }
      else {
         return false;
      }
   }
}