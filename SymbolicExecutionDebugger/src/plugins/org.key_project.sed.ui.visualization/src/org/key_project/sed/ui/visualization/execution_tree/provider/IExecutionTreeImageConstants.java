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

package org.key_project.sed.ui.visualization.execution_tree.provider;

import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEBranchStatement;
import org.key_project.sed.core.model.ISEExceptionalMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalTermination;
import org.key_project.sed.core.model.ISELoopBodyTermination;
import org.key_project.sed.core.model.ISELoopCondition;
import org.key_project.sed.core.model.ISELoopInvariant;
import org.key_project.sed.core.model.ISELoopStatement;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodContract;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISEStatement;
import org.key_project.sed.core.model.ISETermination;
import org.key_project.sed.core.model.ISEThread;

/**
 * <p>
 * This interface provides predefined image constants which can be used by the
 * features for image graphics algorithm.
 * </p>
 * <p>
 * Images itself are provided via {@link ExecutionTreeImageProvider} which
 * is instantiated and managed by Graphiti's extension points.
 * </p>
 * @author Martin Hentschel
 * @see ExecutionTreeImageProvider
 */
public interface IExecutionTreeImageConstants {
   /**
    * The constant prefix of all image keys.
    */
   public static final String PREFIX = "org.key_project.sed.ui.visualization.";
   
   /**
    * Key of the image for {@link ISEBranchCondition}s.
    */
   public static final String IMG_BRANCH_CONDITION = PREFIX + "branchCondition";

   /**
    * Key of the image for {@link ISEBranchStatement}s.
    */
   public static final String IMG_BRANCH_STATEMENT = PREFIX + "branchStatement";

   /**
    * Key of the image for {@link ISEExceptionalTermination}s.
    */
   public static final String IMG_EXCEPTIONAL_TERMINATION = PREFIX + "exceptionalTermination";

   /**
    * Key of the image for {@link ISEExceptionalTermination}s.
    */
   public static final String IMG_EXCEPTIONAL_TERMINATION_NOT_VERIFIED = PREFIX + "exceptionalTerminationNotVerified";

   /**
    * Key of the image for {@link ISELoopCondition}s.
    */
   public static final String IMG_LOOP_CONDITION = PREFIX + "loopCondition";

   /**
    * Key of the image for {@link ISELoopStatement}s.
    */
   public static final String IMG_LOOP_STATEMENT = PREFIX + "loopStatement";

   /**
    * Key of the image for {@link ISEMethodCall}s.
    */
   public static final String IMG_METHOD_CALL = PREFIX + "methodCall";

   /**
    * Key of the image for {@link ISEMethodReturn}s.
    */
   public static final String IMG_METHOD_RETURN = PREFIX + "methodReturn";

   /**
    * Key of the image for {@link ISEExceptionalMethodReturn}s.
    */
   public static final String IMG_EXCEPTIONAL_METHOD_RETURN = PREFIX + "exceptionalMethodReturn";

   /**
    * Key of the image for {@link ISEStatement}s.
    */
   public static final String IMG_STATEMENT = PREFIX + "statement";

   /**
    * Key of the image for {@link ISETermination}s.
    */
   public static final String IMG_TERMINATION = PREFIX + "termination";

   /**
    * Key of the image for {@link ISETermination}s.
    */
   public static final String IMG_TERMINATION_NOT_VERIFIED = PREFIX + "terminationNotVerified";

   /**
    * Key of the image for {@link ISEMethodContract}s.
    */
   public static final String IMG_METHOD_CONTRACT = PREFIX + "methodContract";

   /**
    * Key of the image for {@link ISEMethodContract}s.
    */
   public static final String IMG_METHOD_CONTRACT_NOT_NPC = PREFIX + "methodContractNotNpc";

   /**
    * Key of the image for {@link ISEMethodContract}s.
    */
   public static final String IMG_METHOD_CONTRACT_NOT_PRE = PREFIX + "methodContractNotPre";

   /**
    * Key of the image for {@link ISEMethodContract}s.
    */
   public static final String IMG_METHOD_CONTRACT_NOT_PRE_NOT_NPC = PREFIX + "methodContractNotPreAndNotNpc";

   /**
    * Key of the image for {@link ISELoopInvariant}s.
    */
   public static final String IMG_LOOP_INVARIANT = PREFIX + "loopInvariant";

   /**
    * Key of the image for {@link ISELoopInvariant}s.
    */
   public static final String IMG_LOOP_INVARIANT_INITIALLY_INVALID = PREFIX + "loopInvariantInitiallyInvalid";

   /**
    * Key of the image for {@link ISELoopBodyTermination}s.
    */
   public static final String IMG_LOOP_BODY_TERMINATION = PREFIX + "loopBodyTermination";

   /**
    * Key of the image for {@link ISELoopBodyTermination}s.
    */
   public static final String IMG_LOOP_BODY_TERMINATION_NOT_VERIFIED = PREFIX + "loopBodyTerminationNotVerified";
   
   /**
    * Key of the image for {@link ISEThread}s.
    */
   public static final String IMG_THREAD = PREFIX + "thread";

   /**
    * Key of the image for resume action.
    */
   public static final String IMG_RESUME = PREFIX + "resume";

   /**
    * Key of the image for suspend action.
    */
   public static final String IMG_SUSPEND = PREFIX + "suspend";

   /**
    * Key of the image for step into action.
    */
   public static final String IMG_STEP_INTO = PREFIX + "stepInto";

   /**
    * Key of the image for step over action.
    */
   public static final String IMG_STEP_OVER = PREFIX + "stepOver";

   /**
    * Key of the image for step return action.
    */
   public static final String IMG_STEP_RETURN = PREFIX + "stepReturn";

   /**
    * Key of the image for terminate action.
    */
   public static final String IMG_TERMINATE = PREFIX + "terminate";

   /**
    * Key of the image for visualize state action.
    */
   public static final String IMG_VISUALIZE_STATE = PREFIX + "visualizeState";
}