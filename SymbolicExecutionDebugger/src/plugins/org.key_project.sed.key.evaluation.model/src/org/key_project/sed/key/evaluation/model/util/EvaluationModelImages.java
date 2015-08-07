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

package org.key_project.sed.key.evaluation.model.util;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.key.evaluation.model.Activator;
import org.key_project.util.eclipse.BundleUtil;

/**
 * <p>
 * Provides the images of the Evaluation model.
 * </p>
 * <p>
 * To get an image use one of the constant defined in this class, e.g.<br>
 * {@code EvaluationModelImages.getImage(EvaluationModelImages.JML_LOGO)))}
 * </p>
 * @author Martin Hentschel
 */
public final class EvaluationModelImages {
    /**
     * The key for the JML logo.
     */
    public static final String JML_LOGO = "org.key_project.sed.key.evaluation.model.jmlLogo";
    
    /**
     * The key for the SED logo.
     */
    public static final String SED_LOGO = "org.key_project.sed.key.evaluation.model.sedLogo";
    
    /**
     * The key for the KeY logo.
     */
    public static final String KEY_LOGO = "org.key_project.sed.key.evaluation.model.keyLogo";
    
    /**
     * The key for the thanks image.
     */
    public static final String KEY_THANKS = "org.key_project.sed.key.evaluation.model.keyThanks";
    
    /**
     * The key for the browser image.
     */
    public static final String BROWSER = "org.key_project.sed.key.evaluation.model.browser";
    
    /**
     * The key for the evaluation image.
     */
    public static final String EVALUATION = "org.key_project.sed.key.evaluation.model.evaluation";
    
    /**
     * The key for the evaluation image.
     */
    public static final String KEY_APPLIED_CONTRACTS = "org.key_project.sed.key.evaluation.model.evaluation.key.appliedContracts";
    
    /**
     * The key for the evaluation image.
     */
    public static final String KEY_GOALS = "org.key_project.sed.key.evaluation.model.evaluation.key.goals";
    
    /**
     * The key for the evaluation image.
     */
    public static final String KEY_HIDE_ITERMEDIATE_STEPS = "org.key_project.sed.key.evaluation.model.evaluation.key.hideItermediateSteps";
    
    /**
     * The key for the evaluation image.
     */
    public static final String KEY_PROOF_TREE = "org.key_project.sed.key.evaluation.model.evaluation.key.proofTree";
    
    /**
     * The key for the evaluation image.
     */
    public static final String KEY_SEQUENT = "org.key_project.sed.key.evaluation.model.evaluation.key.sequent";
    
    /**
     * The key for the evaluation image.
     */
    public static final String SED_UP_MEMORY_LAYOUTS = "org.key_project.sed.key.evaluation.model.evaluation.sed.understandingProofAttempts.memoryLayouts";
    
    /**
     * The key for the evaluation image.
     */
    public static final String SED_UP_SET = "org.key_project.sed.key.evaluation.model.evaluation.sed.understandingProofAttempts.set";
    
    /**
     * The key for the evaluation image.
     */
    public static final String SED_UP_TRUTH = "org.key_project.sed.key.evaluation.model.evaluation.sed.understandingProofAttempts.truth";
    
    /**
     * The key for the evaluation image.
     */
    public static final String SED_UP_VARIABLES = "org.key_project.sed.key.evaluation.model.evaluation.sed.understandingProofAttempts.variables";
    
    /**
     * The key for the evaluation image.
     */
    public static final String SED_UP_REACHED = "org.key_project.sed.key.evaluation.model.evaluation.sed.understandingProofAttempts.reachedSourceCode";
    
    /**
     * The key for the Java application logo.
     */
    public static final String JAVA_APPLICATION_LOGO = "org.key_project.sed.key.evaluation.model.javaApplicationLogo";
    
    /**
     * The key for the evaluation image.
     */
    public static final String SED_RC_SET = "org.key_project.sed.key.evaluation.model.evaluation.sed.reviewingCode.set";
    
    /**
     * The key for the evaluation image.
     */
    public static final String SED_RC_VARIABLES = "org.key_project.sed.key.evaluation.model.evaluation.sed.reviewingCode.variables";
    
    /**
     * The key for the evaluation image.
     */
    public static final String SED_RC_REACHED = "org.key_project.sed.key.evaluation.model.evaluation.sed.reviewingCode.reachedSourceCode";
    
    /**
     * The key for the evaluation image.
     */
    public static final String SED_RC_NODE_PROPERTIES = "org.key_project.sed.key.evaluation.model.evaluation.sed.reviewingCode.nodeProperties";
    
    /**
     * Forbid instances.
     */
    private EvaluationModelImages() {
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
        if (JML_LOGO.equals(key)) {
           path = "data/understandingProofAttempts/icons/jml-writing-16x16.png";
        }
        else if (SED_LOGO.equals(key)) {
           path = "data/understandingProofAttempts/icons/symbolic_debug.gif";
        }
        else if (KEY_LOGO.equals(key)) {
           path = "data/understandingProofAttempts/icons/logo16.gif";
        }
        else if (KEY_THANKS.equals(key)) {
           path = "data/understandingProofAttempts/icons/Thanks.png";
        }
        else if (BROWSER.equals(key)) {
           path = "data/browser/icons/internal_browser.gif";
        }
        else if (EVALUATION.equals(key)) {
           path = "data/understandingProofAttempts/icons/evaluation.png";
        }
        else if (KEY_APPLIED_CONTRACTS.equals(key)) {
           path = "data/understandingProofAttempts/icons/KeY_Applied_Contracts.png";
        }
        else if (KEY_GOALS.equals(key)) {
           path = "data/understandingProofAttempts/icons/KeY_Goals.png";
        }
        else if (KEY_HIDE_ITERMEDIATE_STEPS.equals(key)) {
           path = "data/understandingProofAttempts/icons/KeY_Hide_Itermediate_Steps.png";
        }
        else if (KEY_PROOF_TREE.equals(key)) {
           path = "data/understandingProofAttempts/icons/KeY_Proof_Tree.png";
        }
        else if (KEY_SEQUENT.equals(key)) {
           path = "data/understandingProofAttempts/icons/KeY_Sequent.png";
        }
        else if (SED_UP_MEMORY_LAYOUTS.equals(key)) {
           path = "data/understandingProofAttempts/icons/SED_Memory_Layout.png";
        }
        else if (SED_UP_SET.equals(key)) {
           path = "data/understandingProofAttempts/icons/SED_SET.png";
        }
        else if (SED_UP_TRUTH.equals(key)) {
           path = "data/understandingProofAttempts/icons/SED_Truth.png";
        }
        else if (SED_UP_VARIABLES.equals(key)) {
           path = "data/understandingProofAttempts/icons/SED_Variables.png";
        }
        else if (SED_UP_REACHED.equals(key)) {
           path = "data/understandingProofAttempts/icons/SED_Reached.png";
        }
        else if (JAVA_APPLICATION_LOGO.equals(key)) {
           path = "data/reviewingCode/icons/java_app.gif";
        }
        else if (SED_RC_SET.equals(key)) {
           path = "data/reviewingCode/icons/SED_SET.png";
        }
        else if (SED_RC_NODE_PROPERTIES.equals(key)) {
           path = "data/reviewingCode/icons/SED_Node_Properties.png";
        }
        else if (SED_RC_REACHED.equals(key)) {
           path = "data/reviewingCode/icons/SED_Reached.png";
        }
        else if (SED_RC_VARIABLES.equals(key)) {
           path = "data/reviewingCode/icons/SED_Variables.png";
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
    * Returns a scaled version of the {@link Image} registered under the given key.
    * @param key The key.
    * @param scaleFactor The scale factor.
    * @return The new image.
    */
   public static ImageData getImage(String key, int scaleFactor) {
      Image image = getImage(key);
      if (image != null) {
         if (scaleFactor < 0) {
            scaleFactor = scaleFactor * -1;
         }
         ImageData data = image.getImageData();
         int newWidth = data.width / 100 * scaleFactor;
         int newHeight = data.height / 100 * scaleFactor;
         return data.scaledTo(newWidth, newHeight);
      }
      else {
         return null;
      }
   }
}