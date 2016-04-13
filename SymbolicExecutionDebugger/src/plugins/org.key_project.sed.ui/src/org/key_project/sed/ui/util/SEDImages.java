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

package org.key_project.sed.ui.util;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.debug.core.model.IThread;
import org.eclipse.debug.internal.ui.DebugPluginImages;
import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEBranchStatement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEExceptionalMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalTermination;
import org.key_project.sed.core.model.ISELoopBodyTermination;
import org.key_project.sed.core.model.ISELoopCondition;
import org.key_project.sed.core.model.ISELoopInvariant;
import org.key_project.sed.core.model.ISELoopStatement;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodContract;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISETermination;
import org.key_project.sed.ui.Activator;
import org.key_project.util.eclipse.BundleUtil;

/**
 * <p>
 * Provides the images of the Symbolic Execution Debugger based on KeY.
 * </p>
 * <p>
 * To get an image use one of the constant defined in this class, e.g.<br>
 * {@code KeYSEDImages.getImage(KeYSEDImages.LAUNCH_MAIN_TAB_GROUP)))}
 * </p>
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public final class SEDImages {
    /**
     * The key for the image that is used for method calls.
     */
    public static final String METHOD_CALL = "org.key_project.sed.ui.images.methodCall";
    
    /**
     * The key for the image that is used for method return.
     */
    public static final String METHOD_RETURN = "org.key_project.sed.ui.images.methodReturn";
    
    /**
     * The key for the image that is used for exceptional method return.
     */
    public static final String EXCEPTIONAL_METHOD_RETURN = "org.key_project.sed.ui.images.exceptionalMethodReturn";
    
    /**
     * The key for the image that is used for termination.
     */
    public static final String TERMINATION = "org.key_project.sed.ui.images.termination";
    
    /**
     * The key for the image that is used for termination.
     */
    public static final String TERMINATION_NOT_VERIFIED = "org.key_project.sed.ui.images.terminationNotVerified";
    
    /**
     * The key for the image that is used for branch statement.
     */
    public static final String BRANCH_STATEMENT = "org.key_project.sed.ui.images.branchStatement";
    
    /**
     * The key for the image that is used for branch condition.
     */
    public static final String BRANCH_CONDITION = "org.key_project.sed.ui.images.branchCondition";
    
    /**
     * The key for the image that is used for exceptional termination.
     */
    public static final String EXCEPTIONAL_TERMINATION = "org.key_project.sed.ui.images.exceptionalTermination";
    
    /**
     * The key for the image that is used for exceptional termination which is not verified.
     */
    public static final String EXCEPTIONAL_TERMINATION_NOT_VERIFIED = "org.key_project.sed.ui.images.exceptionalTerminationNotVerified";
    
    /**
     * The key for the image that is used for loop statement.
     */
    public static final String LOOP_STATEMENT = "org.key_project.sed.ui.images.loopStatement";
    
    /**
     * The key for the image that is used for loop condition.
     */
    public static final String LOOP_CONDITION = "org.key_project.sed.ui.images.loopCondition";
    
    /**
     * The key for the image that is used for method contract.
     */
    public static final String METHOD_CONTRACT = "org.key_project.sed.ui.images.methodContract";
    
    /**
     * The key for the image that is used for method contract.
     */
    public static final String METHOD_CONTRACT_NOT_PRE = "org.key_project.sed.ui.images.methodContractNotPre";
    
    /**
     * The key for the image that is used for method contract.
     */
    public static final String METHOD_CONTRACT_NOT_NPC = "org.key_project.sed.ui.images.methodContractNotNpc";
    
    /**
     * The key for the image that is used for method contract.
     */
    public static final String METHOD_CONTRACT_NOT_PRE_NOT_NPC = "org.key_project.sed.ui.images.methodContractNotPreNotNpc";
    
    /**
     * The key for the image that is used for loop invariant.
     */
    public static final String LOOP_INVARIANT = "org.key_project.sed.ui.images.loopInvariant";
    
    /**
     * The key for the image that is used for loop invariant.
     */
    public static final String LOOP_INVARIANT_INITIALLY_INVALID = "org.key_project.sed.ui.images.loopInvariantInitiallyInvalid";
    
    /**
     * The key for the image that is used for loop body termination.
     */
    public static final String LOOP_BODY_TERMINATION = "org.key_project.sed.ui.images.loopBodyTermination";
    
    /**
     * The key for the image that is used for KeY watchpoints in the Breakpoints View.
     */
    public static final String KEY_WATCHPOINT = "org.key_project.sed.ui.images.keyWatchpoint";
    
    /**
     * The key for the image that is used for loop body termination not verified.
     */
    public static final String LOOP_BODY_TERMINATION_NOT_VERIFIED = "org.key_project.sed.ui.images.loopBodyTerminationNotVerified";
    
    /**
     * The key for the image that is used to edit an {@link ISEAnnotation}.
     */
    public static final String ANNOTATION_EDIT = "org.key_project.sed.ui.images.annotation.edit";
    
    /**
     * The key for the image that is used to edit an {@link ISEAnnotation}.
     */
    public static final String ANNOTATION_EDIT_WIZARD = "org.key_project.sed.ui.images.annotation.editWizard";
    
    /**
     * The key for the image that is used to move an {@link ISEAnnotation} up.
     */
    public static final String ANNOTATION_MOVE_UP = "org.key_project.sed.ui.images.annotation.moveUp";
    
    /**
     * The key for the image that is used to move an {@link ISEAnnotation} down.
     */
    public static final String ANNOTATION_MOVE_DOWN = "org.key_project.sed.ui.images.annotation.moveDown";
    
    /**
     * The key for the image that is used to delete an {@link ISEAnnotation}.
     */
    public static final String ANNOTATION_DELETE = "org.key_project.sed.ui.images.annotation.delete";

    /**
     * The key for the image that is used to show links of an {@link ISEAnnotation}.
     */
    public static final String ANNOTATION_LINKS = "org.key_project.sed.ui.images.annotation.links";

    /**
     * The key for the image that is used to show links of an {@link ISEAnnotation}.
     */
    public static final String ANNOTATION_LINKS_WIZARD = "org.key_project.sed.ui.images.annotation.linksWizard";

    /**
     * The key for the image that is used to follow an {@link ISEAnnotationLink}.
     */
    public static final String ANNOTATION_GO_TO = "org.key_project.sed.ui.images.annotation.goTo";

    /**
     * The key for the image that is used for symbolic debugging.
     */
    public static final String SYMBOLIC_DEBUG = "org.key_project.sed.ui.images.symbolicDebug";

    /**
     * The key for the image that is used for symbolic debugging.
     */
    public static final String SHOW_ALL_CONSTRAINTS = "org.key_project.sed.ui.images.showAllConstraints";

    /**
     * The key for the image that is used for slicing.
     */
    public static final String SLICE = "org.key_project.sed.ui.images.slicing";

    /**
     * The key for the image that is used for slicing wizard.
     */
    public static final String SLICE_WIZARD = "org.key_project.sed.ui.images.slicingWizard";

    /**
     * The key for the image that is used for searching.
     */
    public static final String SEARCH = "org.key_project.sed.ui.images.search";

    /**
     * The key for the image that is used for search wizard.
     */
    public static final String SEARCH_WIZARD = "org.key_project.sed.ui.images.searchWizard";

    /**
     * The key for the image that is used for comments.
     */
    public static final String COMMENT = "org.key_project.sed.ui.images.comment";

    /**
     * The key for the image that is used for comment wizard.
     */
    public static final String COMMENT_WIZARD = "org.key_project.sed.ui.images.commentWizard";
    
    /**
     * Forbid instances.
     */
    private SEDImages() {
    }
    
    /**
     * Returns the {@link Image} for the given key. The images are shared
     * with other plug-ins. The caller is <b>not</b> responsible for the destruction.
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
        if (METHOD_CALL.equals(key)) {
           path = "icons/method_call.gif";
        }
        else if (METHOD_RETURN.equals(key)) {
           path = "icons/method_return.gif";
        }
        else if (EXCEPTIONAL_METHOD_RETURN.equals(key)) {
           path = "icons/exceptional_method_return.gif";
        }
        else if (TERMINATION.equals(key)) {
           path = "icons/termination.gif";
        }
        else if (TERMINATION_NOT_VERIFIED.equals(key)) {
           path = "icons/termination_not_verified.gif";
        }
        else if (BRANCH_STATEMENT.equals(key)) {
           path = "icons/branch_statement.gif";
        }
        else if (BRANCH_CONDITION.equals(key)) {
           path = "icons/branch_condition.gif";
        }
        else if (EXCEPTIONAL_TERMINATION.equals(key)) {
           path = "icons/exceptional_termination.gif";
        }
        else if (EXCEPTIONAL_TERMINATION_NOT_VERIFIED.equals(key)) {
           path = "icons/exceptional_termination_not_verified.gif";
        }
        else if (LOOP_STATEMENT.equals(key)) {
           path = "icons/loop_statement.gif";
        }
        else if (LOOP_CONDITION.equals(key)) {
           path = "icons/loop_condition.gif";
        }
        else if (METHOD_CONTRACT.equals(key)) {
           path = "icons/method_contract.gif";
        }
        else if (METHOD_CONTRACT_NOT_PRE.equals(key)) {
           path = "icons/method_contract_not_pre.gif";
        }
        else if (METHOD_CONTRACT_NOT_NPC.equals(key)) {
           path = "icons/method_contract_not_npc.gif";
        }
        else if (METHOD_CONTRACT_NOT_PRE_NOT_NPC.equals(key)) {
           path = "icons/method_contract_not_pre_not_npc.gif";
        }
        else if (LOOP_INVARIANT.equals(key)) {
           path = "icons/loop_invariant.gif";
        }
        else if (LOOP_INVARIANT_INITIALLY_INVALID.equals(key)) {
           path = "icons/loop_invariant_initially_invalid.gif";
        }
        else if (LOOP_BODY_TERMINATION.equals(key)) {
           path = "icons/loop_body_termination.gif";
        }else if(KEY_WATCHPOINT.equals(key)){
           path = "icons/watchpoint.gif";
        }
        else if (LOOP_BODY_TERMINATION_NOT_VERIFIED.equals(key)) {
           path = "icons/exceptional_termination_not_verified.gif";
        }
        else if (ANNOTATION_EDIT.equals(key)) {
           path = "icons/write_obj.gif";
        }
        else if (ANNOTATION_EDIT_WIZARD.equals(key)) {
           path = "icons/write_wizard.png";
        }
        else if (ANNOTATION_MOVE_UP.equals(key)) {
           path = "icons/up.gif";
        }
        else if (ANNOTATION_MOVE_DOWN.equals(key)) {
           path = "icons/down.gif";
        }
        else if (ANNOTATION_DELETE.equals(key)) {
           path = "icons/rem_co.gif";
        }
        else if (ANNOTATION_LINKS.equals(key)) {
           path = "icons/links_obj.gif";
        }
        else if (ANNOTATION_LINKS_WIZARD.equals(key)) {
           path = "icons/links_wizard.png";
        }
        else if (ANNOTATION_GO_TO.equals(key)) {
           path = "icons/follow_annotation_link.gif";
        }
        else if (SYMBOLIC_DEBUG.equals(key)) {
           path = "icons/symbolic_debug.gif";
        }
        else if (SHOW_ALL_CONSTRAINTS.equals(key)) {
           path = "icons/show_all_constraints.gif";
        }
        else if (SLICE.equals(key)) {
           path = "icons/slice.gif";
        }
        else if (SLICE_WIZARD.equals(key)) {
           path = "icons/slice_wizard.png";
        }
        else if (SEARCH.equals(key)) {
           path = "icons/search.gif";
        }
        else if (SEARCH_WIZARD.equals(key)) {
           path = "icons/search_wizard.png";
        }
        else if (COMMENT.equals(key)) {
           path = "icons/comment.gif";
        }
        else if (COMMENT_WIZARD.equals(key)) {
           path = "icons/comment_wizard.png";
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
    
    /**
     * Returns the type icon of the given {@link ISENode}.
     * @param element The {@link ISENode} to get type icon for.
     * @return The type icon.
     */
    public static Image getNodeImage(ISENode element) {
       if (element instanceof ISEMethodCall) {
          return getImage(SEDImages.METHOD_CALL);
       }
       else if (element instanceof ISEMethodReturn) {
          return getImage(SEDImages.METHOD_RETURN);
       }
       else if (element instanceof ISEExceptionalMethodReturn) {
          return getImage(SEDImages.EXCEPTIONAL_METHOD_RETURN);
       }
       else if (element instanceof ISEExceptionalTermination) {
          ISEExceptionalTermination node = (ISEExceptionalTermination)element;
          if (node.isVerified()) {
             return getImage(SEDImages.EXCEPTIONAL_TERMINATION);
          }
          else {
             return getImage(SEDImages.EXCEPTIONAL_TERMINATION_NOT_VERIFIED);
          }
       }
       else if (element instanceof ISELoopBodyTermination) {
          ISELoopBodyTermination node = (ISELoopBodyTermination)element;
          if (node.isVerified()) {
             return getImage(SEDImages.LOOP_BODY_TERMINATION);
          }
          else {
             return getImage(SEDImages.LOOP_BODY_TERMINATION_NOT_VERIFIED);
          }
       }
       else if (element instanceof ISETermination) {
          ISETermination node = (ISETermination)element;
          if (node.isVerified()) {
             return getImage(SEDImages.TERMINATION);
          }
          else {
             return getImage(SEDImages.TERMINATION_NOT_VERIFIED);
          }
       }
       else if (element instanceof ISEBranchCondition) {
          return getImage(SEDImages.BRANCH_CONDITION);
       }
       else if (element instanceof ISEBranchStatement) {
          return getImage(SEDImages.BRANCH_STATEMENT);
       }
       else if (element instanceof ISELoopStatement) {
          return getImage(SEDImages.LOOP_STATEMENT);
       }
       else if (element instanceof ISELoopCondition) {
          return getImage(SEDImages.LOOP_CONDITION);
       }
       else if (element instanceof ISEMethodContract) {
          ISEMethodContract node = (ISEMethodContract)element;
          if (node.isPreconditionComplied()) {
             if (!node.hasNotNullCheck() || node.isNotNullCheckComplied()) {
                return getImage(SEDImages.METHOD_CONTRACT);
             }
             else {
                return getImage(SEDImages.METHOD_CONTRACT_NOT_NPC);
             }
          }
          else {
             if (!node.hasNotNullCheck() || node.isNotNullCheckComplied()) {
                return getImage(SEDImages.METHOD_CONTRACT_NOT_PRE);
             }
             else {
                return getImage(SEDImages.METHOD_CONTRACT_NOT_PRE_NOT_NPC);
             }
          }
       }
       else if (element instanceof ISELoopInvariant) {
          ISELoopInvariant node = (ISELoopInvariant)element;
          if (node.isInitiallyValid()) {
             return getImage(SEDImages.LOOP_INVARIANT);
          }
          else {
             return getImage(SEDImages.LOOP_INVARIANT_INITIALLY_INVALID);
          }
       }
       else if (element instanceof IThread) {
          // Oriented on org.eclipse.debug.internal.ui.DefaultLabelProvider#getImageKey(Object)
          IThread thread = (IThread) element;
          if (thread.isSuspended()) {
             return DebugPluginImages.getImage(IDebugUIConstants.IMG_OBJS_THREAD_SUSPENDED);
          }
          else if (thread.isTerminated()) {
             return DebugPluginImages.getImage(IDebugUIConstants.IMG_OBJS_THREAD_TERMINATED);
          }
          else {
             return DebugPluginImages.getImage(IDebugUIConstants.IMG_OBJS_THREAD_RUNNING);
          }
       }
       else {
          return DebugUIPlugin.getDefaultLabelProvider().getImage(element);
       }
    }
}