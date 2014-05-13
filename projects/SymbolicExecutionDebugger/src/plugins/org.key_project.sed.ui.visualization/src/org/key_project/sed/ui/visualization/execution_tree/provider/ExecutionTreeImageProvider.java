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

import org.eclipse.graphiti.ui.platform.AbstractImageProvider;
import org.eclipse.graphiti.ui.platform.IImageProvider;

/**
 * <p>
 * {@link IImageProvider} specific implementation for execution tree diagrams.
 * </p>
 * <p>
 * The constants of provided images are specified via interface {@link IExecutionTreeImageConstants}.
 * </p>
 * <p>
 * This class is instantiated an manged by Graphiti's extension points.
 * </p>
 * @author Martin Hentschel
 * @see IExecutionTreeImageConstants
 */
public class ExecutionTreeImageProvider extends AbstractImageProvider {
   /**
    * Path to the folder which contains the provided images.
    */
   private static final String ROOT_FOLDER_FOR_IMG = "icons/";
   
   /**
    * Path to the folder which contains the provided images.
    */
   private static final String ROOT_FOLDER_FOR_IMG_DEBUG_UI = "icons/org.eclipse.debug.ui/";

   /**
    * {@inheritDoc}
    */
   @Override
   protected void addAvailableImages() {
       addImageFilePath(IExecutionTreeImageConstants.IMG_BRANCH_CONDITION, ROOT_FOLDER_FOR_IMG + "branch_condition.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_BRANCH_STATEMENT, ROOT_FOLDER_FOR_IMG + "branch_statement.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_EXCEPTIONAL_TERMINATION, ROOT_FOLDER_FOR_IMG + "exceptional_termination.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_EXCEPTIONAL_TERMINATION_NOT_VERIFIED, ROOT_FOLDER_FOR_IMG + "exceptional_termination_not_verified.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_LOOP_CONDITION, ROOT_FOLDER_FOR_IMG + "loop_condition.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_LOOP_STATEMENT, ROOT_FOLDER_FOR_IMG + "loop_statement.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_METHOD_CALL, ROOT_FOLDER_FOR_IMG + "method_call.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_METHOD_RETURN, ROOT_FOLDER_FOR_IMG + "method_return.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_STATEMENT, ROOT_FOLDER_FOR_IMG + "statement.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_TERMINATION, ROOT_FOLDER_FOR_IMG + "termination.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_TERMINATION_NOT_VERIFIED, ROOT_FOLDER_FOR_IMG + "termination_not_verified.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_THREAD, ROOT_FOLDER_FOR_IMG + "thread.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_METHOD_CONTRACT, ROOT_FOLDER_FOR_IMG + "method_contract.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_METHOD_CONTRACT_NOT_NPC, ROOT_FOLDER_FOR_IMG + "method_contract_not_npc.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_METHOD_CONTRACT_NOT_PRE, ROOT_FOLDER_FOR_IMG + "method_contract_not_pre.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_METHOD_CONTRACT_NOT_PRE_NOT_NPC, ROOT_FOLDER_FOR_IMG + "method_contract_not_pre_not_npc.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_LOOP_INVARIANT, ROOT_FOLDER_FOR_IMG + "loop_invariant.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_LOOP_INVARIANT_INITIALLY_INVALID, ROOT_FOLDER_FOR_IMG + "loop_invariant _initially_invalid.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_LOOP_BODY_TERMINATION, ROOT_FOLDER_FOR_IMG + "loop_body_termination.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_LOOP_BODY_TERMINATION_NOT_VERIFIED, ROOT_FOLDER_FOR_IMG + "loop_body_termination_not_verified.gif");

       addImageFilePath(IExecutionTreeImageConstants.IMG_RESUME, ROOT_FOLDER_FOR_IMG_DEBUG_UI + "resume_co.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_SUSPEND, ROOT_FOLDER_FOR_IMG_DEBUG_UI + "suspend_co.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_STEP_INTO, ROOT_FOLDER_FOR_IMG_DEBUG_UI + "stepinto_co.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_STEP_OVER, ROOT_FOLDER_FOR_IMG_DEBUG_UI + "stepover_co.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_STEP_RETURN, ROOT_FOLDER_FOR_IMG_DEBUG_UI + "stepreturn_co.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_TERMINATE, ROOT_FOLDER_FOR_IMG_DEBUG_UI + "terminate_co.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_VISUALIZE_STATE, ROOT_FOLDER_FOR_IMG + "object_diagram.gif");
   }
}