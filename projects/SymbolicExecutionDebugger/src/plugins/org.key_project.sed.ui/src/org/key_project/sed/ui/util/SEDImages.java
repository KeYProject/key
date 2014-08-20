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

import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchStatement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDExceptionalMethodReturn;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDLoopBodyTermination;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDLoopInvariant;
import org.key_project.sed.core.model.ISEDLoopStatement;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodContract;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDTermination;
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
     * The key for the image that is used to edit an {@link ISEDAnnotation}.
     */
    public static final String ANNOTATION_EDIT = "org.key_project.sed.ui.images.annotation.edit";
    
    /**
     * The key for the image that is used to move an {@link ISEDAnnotation} up.
     */
    public static final String ANNOTATION_MOVE_UP = "org.key_project.sed.ui.images.annotation.moveUp";
    
    /**
     * The key for the image that is used to move an {@link ISEDAnnotation} down.
     */
    public static final String ANNOTATION_MOVE_DOWN = "org.key_project.sed.ui.images.annotation.moveDown";
    
    /**
     * The key for the image that is used to delete an {@link ISEDAnnotation}.
     */
    public static final String ANNOTATION_DELETE = "org.key_project.sed.ui.images.annotation.delete";

    /**
     * The key for the image that is used to show links of an {@link ISEDAnnotation}.
     */
    public static final String ANNOTATION_LINKS = "org.key_project.sed.ui.images.annotation.links";

    /**
     * The key for the image that is used to follow an {@link ISEDAnnotationLink}.
     */
    public static final String ANNOTATION_GO_TO = "org.key_project.sed.ui.images.annotation.goTo";

    /**
     * The key for the image that is used for symbolic debugging.
     */
    public static final String SYMBOLIC_DEBUG = "org.key_project.sed.ui.images.symbolicDebug";
    
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
           path = "icons/loop_invariant _initially_invalid.gif";
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
        else if (ANNOTATION_GO_TO.equals(key)) {
           path = "icons/follow_annotation_link.gif";
        }
        else if (SYMBOLIC_DEBUG.equals(key)) {
           path = "icons/symbolic_debug.gif";
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
     * Disposes all contained images. This method is automatically called
     * when the plug-in is unloaded from the {@link Activator}.
     * There is no need to call it from any other place!
     */
    public static void disposeImages() {
       Display display = Display.getDefault();
       if (!display.isDisposed()) {
          display.syncExec(new Runnable() {
            @Override
            public void run() {
               ImageRegistry registry = Activator.getDefault().getImageRegistry();
               registry.remove(ANNOTATION_DELETE);
               registry.remove(ANNOTATION_EDIT);
               registry.remove(ANNOTATION_GO_TO);
               registry.remove(ANNOTATION_LINKS);
               registry.remove(ANNOTATION_MOVE_DOWN);
               registry.remove(ANNOTATION_MOVE_UP);
               registry.remove(BRANCH_CONDITION);
               registry.remove(BRANCH_STATEMENT);
               registry.remove(EXCEPTIONAL_METHOD_RETURN);
               registry.remove(EXCEPTIONAL_TERMINATION);
               registry.remove(EXCEPTIONAL_TERMINATION_NOT_VERIFIED);
               registry.remove(KEY_WATCHPOINT);
               registry.remove(LOOP_BODY_TERMINATION);
               registry.remove(LOOP_BODY_TERMINATION_NOT_VERIFIED);
               registry.remove(LOOP_CONDITION);
               registry.remove(LOOP_INVARIANT);
               registry.remove(LOOP_INVARIANT_INITIALLY_INVALID);
               registry.remove(LOOP_STATEMENT);
               registry.remove(METHOD_CALL);
               registry.remove(METHOD_CONTRACT);
               registry.remove(METHOD_CONTRACT_NOT_NPC);
               registry.remove(METHOD_CONTRACT_NOT_PRE);
               registry.remove(METHOD_CONTRACT_NOT_PRE_NOT_NPC);
               registry.remove(METHOD_RETURN);
               registry.remove(TERMINATION);
               registry.remove(TERMINATION_NOT_VERIFIED);
               registry.remove(SYMBOLIC_DEBUG);
            }
         });
       }
    }
    
    /**
     * Returns the type icon of the given {@link ISEDDebugNode}.
     * @param element The {@link ISEDDebugNode} to get type icon for.
     * @return The type icon.
     */
    public static Image getNodeImage(ISEDDebugNode element) {
       if (element instanceof ISEDMethodCall) {
          return getImage(SEDImages.METHOD_CALL);
       }
       else if (element instanceof ISEDMethodReturn) {
          return getImage(SEDImages.METHOD_RETURN);
       }
       else if (element instanceof ISEDExceptionalMethodReturn) {
          return getImage(SEDImages.EXCEPTIONAL_METHOD_RETURN);
       }
       else if (element instanceof ISEDExceptionalTermination) {
          ISEDExceptionalTermination node = (ISEDExceptionalTermination)element;
          if (node.isVerified()) {
             return getImage(SEDImages.EXCEPTIONAL_TERMINATION);
          }
          else {
             return getImage(SEDImages.EXCEPTIONAL_TERMINATION_NOT_VERIFIED);
          }
       }
       else if (element instanceof ISEDLoopBodyTermination) {
          ISEDLoopBodyTermination node = (ISEDLoopBodyTermination)element;
          if (node.isVerified()) {
             return getImage(SEDImages.LOOP_BODY_TERMINATION);
          }
          else {
             return getImage(SEDImages.LOOP_BODY_TERMINATION_NOT_VERIFIED);
          }
       }
       else if (element instanceof ISEDTermination) {
          ISEDTermination node = (ISEDTermination)element;
          if (node.isVerified()) {
             return getImage(SEDImages.TERMINATION);
          }
          else {
             return getImage(SEDImages.TERMINATION_NOT_VERIFIED);
          }
       }
       else if (element instanceof ISEDBranchCondition) {
          return getImage(SEDImages.BRANCH_CONDITION);
       }
       else if (element instanceof ISEDBranchStatement) {
          return getImage(SEDImages.BRANCH_STATEMENT);
       }
       else if (element instanceof ISEDLoopStatement) {
          return getImage(SEDImages.LOOP_STATEMENT);
       }
       else if (element instanceof ISEDLoopCondition) {
          return getImage(SEDImages.LOOP_CONDITION);
       }
       else if (element instanceof ISEDMethodContract) {
          ISEDMethodContract node = (ISEDMethodContract)element;
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
       else if (element instanceof ISEDLoopInvariant) {
          ISEDLoopInvariant node = (ISEDLoopInvariant)element;
          if (node.isInitiallyValid()) {
             return getImage(SEDImages.LOOP_INVARIANT);
          }
          else {
             return getImage(SEDImages.LOOP_INVARIANT_INITIALLY_INVALID);
          }
       }
       else {
          return DebugUIPlugin.getDefaultLabelProvider().getImage(element);
       }
    }
}