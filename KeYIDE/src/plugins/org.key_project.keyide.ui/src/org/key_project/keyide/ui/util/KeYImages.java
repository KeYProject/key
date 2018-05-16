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

package org.key_project.keyide.ui.util;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.keyide.ui.Activator;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.util.eclipse.BundleUtil;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

/**
 * <p>
 * Provides the images of the Symbolic Execution Debugger based on KeY.
 * </p>
 * <p>
 * To get an image use one of the constant defined in this class, e.g.<br>
 * {@code KeYSEDImages.getImage(KeYSEDImages.LAUNCH_MAIN_TAB_GROUP)))}
 * </p>
 * @author Martin Hentschel, Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public final class KeYImages {
   /**
    * The key of a {@link BranchFolder} image.
    */
   public static final String FOLDER = "org.key_project.keyide.ui.images.folder";
   
   /**
    * The key of a proved {@link BranchFolder} image.
    */
   public static final String FOLDER_PROVED = "org.key_project.keyide.ui.images.folderProved";
   
   /**
    * The key of a {@link Node} image.
    */
   public static final String NODE = "org.key_project.keyide.ui.images.node";
   
   /**
    * The key of a {@link Node} image.
    */
   public static final String NODE_INTERACTIVE = "org.key_project.keyide.ui.images.nodeInteractive";
   
   /**
    * The key of a proved {@link Node} image.
    */
   public static final String NODE_PROVED = "org.key_project.keyide.ui.images.nodeProved";
   
   /**
    * The key for the image that is used for method calls.
    */
   public static final String METHOD_CALL = "org.key_project.keyide.ui.images.methodCall";
   
   /**
    * The key for the image that is used for method return.
    */
   public static final String METHOD_RETURN = "org.key_project.keyide.ui.images.methodReturn";
   
   /**
    * The key for the image that is used for exceptional method return.
    */
   public static final String EXCEPTIONAL_METHOD_RETURN = "org.key_project.keyide.ui.images.exceptionalMethodReturn";
   
   /**
    * The key for the image that is used for termination.
    */
   public static final String TERMINATION = "org.key_project.keyide.ui.images.termination";
   
   /**
    * The key for the image that is used for termination.
    */
   public static final String TERMINATION_NOT_VERIFIED = "org.key_project.keyide.ui.images.terminationNotVerified";
   
   /**
    * The key for the image that is used for branch statement.
    */
   public static final String BRANCH_STATEMENT = "org.key_project.keyide.ui.images.branchStatement";
   
   /**
    * The key for the image that is used for branch condition.
    */
   public static final String BRANCH_CONDITION = "org.key_project.keyide.ui.images.branchCondition";
   
   /**
    * The key for the image that is used for exceptional termination.
    */
   public static final String EXCEPTIONAL_TERMINATION = "org.key_project.keyide.ui.images.exceptionalTermination";
   
   /**
    * The key for the image that is used for exceptional termination which is not verified.
    */
   public static final String EXCEPTIONAL_TERMINATION_NOT_VERIFIED = "org.key_project.keyide.ui.images.exceptionalTerminationNotVerified";
   
   /**
    * The key for the image that is used for loop statement.
    */
   public static final String LOOP_STATEMENT = "org.key_project.keyide.ui.images.loopStatement";
   
   /**
    * The key for the image that is used for loop condition.
    */
   public static final String LOOP_CONDITION = "org.key_project.keyide.ui.images.loopCondition";
   
   /**
    * The key for the image that is used for method contract.
    */
   public static final String METHOD_CONTRACT = "org.key_project.keyide.ui.images.methodContract";
   
   /**
    * The key for the image that is used for method contract.
    */
   public static final String METHOD_CONTRACT_NOT_PRE = "org.key_project.keyide.ui.images.methodContractNotPre";
   
   /**
    * The key for the image that is used for method contract.
    */
   public static final String METHOD_CONTRACT_NOT_NPC = "org.key_project.keyide.ui.images.methodContractNotNpc";
   
   /**
    * The key for the image that is used for method contract.
    */
   public static final String METHOD_CONTRACT_NOT_PRE_NOT_NPC = "org.key_project.keyide.ui.images.methodContractNotPreNotNpc";
   
   /**
    * The key for the image that is used for loop invariant.
    */
   public static final String LOOP_INVARIANT = "org.key_project.keyide.ui.images.loopInvariant";
   
   /**
    * The key for the image that is used for loop invariant.
    */
   public static final String LOOP_INVARIANT_INITIALLY_INVALID = "org.key_project.keyide.ui.images.loopInvariantInitiallyInvalid";
   
   /**
    * The key for the image that is used for loop body termination.
    */
   public static final String LOOP_BODY_TERMINATION = "org.key_project.keyide.ui.images.loopBodyTermination";
   
   /**
    * The key for the image that is used for loop body termination not verified.
    */
   public static final String LOOP_BODY_TERMINATION_NOT_VERIFIED = "org.key_project.keyide.ui.images.loopBodyTerminationNotVerified";
   
   /**
    * The key for the image that is used for statements.
 	*/
   public static final String STATEMENT = "org.key_project.keyide.ui.images.statement";
   
   /**
    * The key for the image that is used for threads.
    */
   public static final String THREAD = "org.key_project.keyide.ui.images.thread";
   
   /**
    * The key for the image that is used for block contracts.
    */
   public static final String BLOCK_CONTRACT = "org.key_project.keyide.ui.images.blockContract";
   
   /**
    * The key for the image that is used for block contracts.
    */
   public static final String BLOCK_CONTRACT_NOT_PRE = "org.key_project.keyide.ui.images.blockContractNotPre";
   
   /**
    * The key for the image that is used for loop body termination.
    */
   public static final String BLOCK_CONTRACT_TERMINATION = "org.key_project.keyide.ui.images.blockContractTermination";
   
   /**
    * The key for the image that is used for loop body termination.
    */
   public static final String BLOCK_CONTRACT_TERMINATION_NOT_VERIFIED = "org.key_project.keyide.ui.images.blockContractTerminationNotVerified";
   
   /**
    * The key for the image that is used for exceptional loop body termination.
    */
   public static final String BLOCK_CONTRACT_EXCEPTIONAL_TERMINATION = "org.key_project.keyide.ui.images.blockContractExceptionalTermination";
   
   /**
    * The key for the image that is used for exceptional loop body termination.
    */
   public static final String BLOCK_CONTRACT_EXCEPTIONAL_TERMINATION_NOT_VERIFIED = "org.key_project.keyide.ui.images.blockContractExceptinalTerminationNotVerified";

   /**
    * The key for the image that is used to jump to the previous search result.
    */
   public static final String JUMP_TO_PREVIOUS_SEARCH_RESULT = "org.key_project.keyide.ui.images.previousSearchResult";

   /**
    * The key for the image that is used to jump to the next search result.
    */
   public static final String JUMP_TO_NEXT_SEARCH_RESULT = "org.key_project.keyide.ui.images.nextSearchResult";

   /**
    * The key for the image that is used to close the search result.
    */
   public static final String CLOSE_SEARCH = "org.key_project.keyide.ui.images.closeSearch";

   /**
    * The key for the image that is used for disabled {@link Goal}s.
    */
   public static final String DISABLED_GOAL = "org.key_project.keyide.ui.images.disabledGoal";

   /**
    * The key for the image that is used for the edit notes wizard.
    */
   public static final String EDIT_NOTES_WIZARD = "org.key_project.keyide.ui.images.editNotesWizard";
   
   /**
    * Forbid instances.
    */
   private KeYImages(){
   }

   /**
    * Returns the {@link Image} for the given key. The caller is <b>not</b> responsible for the destruction.
    * For this reason it is forbidden to call {@link Image#dispose()} on
    * a used {@link Image}.
    * @param key The key that identifies the needed {@link Image}. Use one of the constants provided by this class.
    * @return The {@link Image} or {@code null} if it was not possible to get it.
    */
   public static Image getImage(String key) {
      ImageRegistry imageRegistry = Activator.getDefault().getImageRegistry();  
      Image image = imageRegistry.get(key);
      if (image == null) {
          synchronized (imageRegistry) { // Make sure that the image is created only once
             image = imageRegistry.get(key); // Make sure that the image is still not available
             if (image == null) { 
                image = createImage(key);
                if (image != null) {
                   imageRegistry.put(key, image);
                }
             }
          }
      }
      return image;
   }
   
   /**
    * Returns the {@link ImageDescriptor} for the given key.
    * @param key The key.
    * @return The {@link ImageDescriptor} or {@code null} if not available.
    */
   public static ImageDescriptor getImageDescriptor(String key) {
      ImageRegistry imageRegistry = Activator.getDefault().getImageRegistry();
      ImageDescriptor descriptor = imageRegistry.getDescriptor(key);
      if (descriptor == null) {
         synchronized (imageRegistry) { // Make sure that the image is created only once
            descriptor = imageRegistry.getDescriptor(key); // Make sure that the image is still not available
            if (descriptor == null) {
               Image image = createImage(key);
               imageRegistry.put(key, image);
               descriptor = imageRegistry.getDescriptor(key);
            }
         } 
      }
      return descriptor;
   }
   
   /**
    * Creates an {@link Image} for the given key.
    * @param key The key that identifies the image. Use one of the constants provided by this class.
    * @return The created {@link Image} or {@code null} if it was not possible.
    */
   protected static Image createImage(String key) {
       // Compute path to image in bundle.
       String path = null;
       if (FOLDER.equals(key)) {
          path = "icons/folder16.png";
       }
       else if (FOLDER_PROVED.equals(key)) {
          path = "icons/folderproved16.png";
       }
       else if (NODE.equals(key)) {
          path = "icons/ekey-mono16.png";
       }
       else if (NODE_PROVED.equals(key)) {
          path = "icons/keyproved16.png";
       }
       else if (NODE_INTERACTIVE.equals(key)) {
          path = "icons/interactiveAppLogo16.png";
       }
       else if (METHOD_CALL.equals(key)) {
          path = "icons/SEDIcons/method_call.gif";
       }
       else if (METHOD_RETURN.equals(key)) {
          path = "icons/SEDIcons/method_return.gif";
       }
       else if (EXCEPTIONAL_METHOD_RETURN.equals(key)) {
          path = "icons/SEDIcons/exceptional_method_return.gif";
       }
       else if (TERMINATION.equals(key)) {
          path = "icons/SEDIcons/termination.gif";
       }
       else if (TERMINATION_NOT_VERIFIED.equals(key)) {
          path = "icons/SEDIcons/termination_not_verified.gif";
       }
       else if (BRANCH_STATEMENT.equals(key)) {
          path = "icons/SEDIcons/branch_statement.gif";
       }
       else if (BRANCH_CONDITION.equals(key)) {
          path = "icons/SEDIcons/branch_condition.gif";
       }
       else if (EXCEPTIONAL_TERMINATION.equals(key)) {
          path = "icons/SEDIcons/exceptional_termination.gif";
       }
       else if (EXCEPTIONAL_TERMINATION_NOT_VERIFIED.equals(key)) {
          path = "icons/SEDIcons/exceptional_termination_not_verified.gif";
       }
       else if (LOOP_STATEMENT.equals(key)) {
          path = "icons/SEDIcons/loop_statement.gif";
       }
       else if (LOOP_CONDITION.equals(key)) {
          path = "icons/SEDIcons/loop_condition.gif";
       }
       else if (METHOD_CONTRACT.equals(key)) {
          path = "icons/SEDIcons/method_contract.gif";
       }
       else if (METHOD_CONTRACT_NOT_PRE.equals(key)) {
          path = "icons/SEDIcons/method_contract_not_pre.gif";
       }
       else if (METHOD_CONTRACT_NOT_NPC.equals(key)) {
          path = "icons/SEDIcons/method_contract_not_npc.gif";
       }
       else if (METHOD_CONTRACT_NOT_PRE_NOT_NPC.equals(key)) {
          path = "icons/SEDIcons/method_contract_not_pre_not_npc.gif";
       }
       else if (LOOP_INVARIANT.equals(key)) {
          path = "icons/SEDIcons/loop_invariant.gif";
       }
       else if (LOOP_INVARIANT_INITIALLY_INVALID.equals(key)) {
          path = "icons/SEDIcons/loop_invariant _initially_invalid.gif";
       }
       else if (LOOP_BODY_TERMINATION.equals(key)) {
          path = "icons/SEDIcons/loop_body_termination.gif";
       }
       else if (LOOP_BODY_TERMINATION_NOT_VERIFIED.equals(key)) {
          path = "icons/SEDIcons/exceptional_termination_not_verified.gif";
       }
       else if (STATEMENT.equals(key)) {
       	  path = "icons/SEDIcons/statement.gif";
       }
       else if (THREAD.equals(key)) {
    	  path = "icons/SEDIcons/thread.gif";
       }
       else if (BLOCK_CONTRACT.equals(key)) {
          path = "icons/SEDIcons/block_contract.gif";
       }
       else if (BLOCK_CONTRACT_NOT_PRE.equals(key)) {
          path = "icons/SEDIcons/block_contract_not_pre.gif";
       }
       else if (BLOCK_CONTRACT_TERMINATION.equals(key)) {
          path = "icons/SEDIcons/block_contract_termination.gif";
       }
       else if (BLOCK_CONTRACT_TERMINATION_NOT_VERIFIED.equals(key)) {
          path = "icons/SEDIcons/block_contract_termination_not_verified.gif";
       }
       else if (BLOCK_CONTRACT_EXCEPTIONAL_TERMINATION.equals(key)) {
          path = "icons/SEDIcons/block_contract_exceptional_termination.gif";
       }
       else if (BLOCK_CONTRACT_EXCEPTIONAL_TERMINATION_NOT_VERIFIED.equals(key)) {
          path = "icons/SEDIcons/block_contract_exceptional_termination_not_verified.gif";
       }
       else if (JUMP_TO_PREVIOUS_SEARCH_RESULT.equals(key)) {
          path = "icons/previousFoundProofNode.png";
       }
       else if (JUMP_TO_NEXT_SEARCH_RESULT.equals(key)) {
          path = "icons/nextFoundProofNode.png";
       }
       else if (CLOSE_SEARCH.equals(key)) {
          path = "icons/close_view.gif";
       }
       else if (DISABLED_GOAL.equals(key)) {
          path = "icons/keyinteractive.png";
       }
       else if (EDIT_NOTES_WIZARD.equals(key)) {
          path = "icons/editNotes_wizard.png";
       }
       // Load image if possible
       if (path != null) {
          InputStream in = null;
          try {
             in = BundleUtil.openInputStream(Activator.PLUGIN_ID, path);
             return new Image(Display.getDefault(), in);
          }
          catch (IOException e) {
             LogUtil.getLogger().logError(e);
             return null;
          }
          finally {
             try {
                if (in != null) {
                   in.close();
               }
            }
            catch (IOException e) {
               LogUtil.getLogger().logError(e);
            }
          }
       }
       else {
          return null;
       }
   }
}