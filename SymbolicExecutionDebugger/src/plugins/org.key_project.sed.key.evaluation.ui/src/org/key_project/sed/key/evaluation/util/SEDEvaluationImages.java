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

package org.key_project.sed.key.evaluation.util;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.jface.fieldassist.FieldDecorationRegistry;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.widgets.Display;
import org.key_project.sed.key.evaluation.Activator;
import org.key_project.util.eclipse.BundleUtil;

/**
 * <p>
 * Provides the images of the evaluation of the Symbolic Execution Debugger based on KeY.
 * </p>
 * <p>
 * To get an image use one of the constant defined in this class, e.g.<br>
 * {@code SEDEvaluationImages.getImage(SEDEvaluationImages.LAUNCH_MAIN_TAB_GROUP)))}
 * </p>
 * @author Martin Hentschel
 */
public final class SEDEvaluationImages {
   /**
    * The key for the image that is used for the evaluation.
    */
   public static final String EVALUATION = "org.key_project.sed.key.evaluation.ui.evaluation";
   /**
    * The key for the image that is used for the evaluation.
    */
   public static final String EVALUATION_KEY = "org.key_project.sed.key.evaluation.ui.evaluationKeY";
   /**
    * The key for the image that is used for the evaluation.
    */
   public static final String EVALUATION_JAVA = "org.key_project.sed.key.evaluation.ui.evaluationJava";
   
    /**
     * The key for the image that is used for the evaluation wizard.
     */
    public static final String EVALUATION_WIZARD = "org.key_project.sed.key.evaluation.ui.evaluationWizard";
   
    /**
     * The key for the image that is used for the evaluation wizard.
     */
    public static final String EVALUATION_WIZARD_KEY = "org.key_project.sed.key.evaluation.ui.evaluationWizardKeY";
   
    /**
     * The key for the image that is used for the evaluation wizard.
     */
    public static final String EVALUATION_WIZARD_JAVA = "org.key_project.sed.key.evaluation.ui.evaluationWizardJava";
    
    /**
     * The key for the emoticon fantasy dreaming.
     */
    public static final String EMOTICON_FANTASY_DREAMING = "org.key_project.sed.key.evaluation.ui.emoticonFantasyDreaming";
    
    /**
     * The key for the emoticon fantasy dreaming.
     */
    public static final String EMOTICON_FANTASY_DREAMING_ERROR = "org.key_project.sed.key.evaluation.ui.emoticonFantasyDreamingError";

    /**
     * The key for the emoticon omg.
     */
    public static final String EMOTICON_OMG = "org.key_project.sed.key.evaluation.ui.emoticonOmg";

    /**
     * The key for the emoticon omg.
     */
    public static final String EMOTICON_OMG_ERROR = "org.key_project.sed.key.evaluation.ui.emoticonOmgError";

    /**
     * The key for the emoticon wow dude.
     */
    public static final String EMOTICON_WOW_DUDE = "org.key_project.sed.key.evaluation.ui.emoticonWowDude";

    /**
     * The key for the emoticon wow dude.
     */
    public static final String EMOTICON_WOW_DUDE_ERROR = "org.key_project.sed.key.evaluation.ui.emoticonWowDudeError";

    /**
     * The key for the pin shell image.
     */
    public static final String PIN_SHELL = "org.key_project.sed.key.evaluation.ui.pinShell";

    /**
     * The key for the reset workbench image.
     */
    public static final String RESET_WORKBENCH = "org.key_project.sed.key.evaluation.ui.resetWorkbench";
    
    /**
     * Forbid instances.
     */
    private SEDEvaluationImages() {
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
        if (EVALUATION.equals(key)) {
           path = "icons/evaluation.png";
        }
        else if (EVALUATION_KEY.equals(key)) {
           path = "icons/evaluation_KeY.png";
        }
        else if (EVALUATION_JAVA.equals(key)) {
           path = "icons/evaluation_Java.png";
        }
        else if (EVALUATION_WIZARD.equals(key)) {
           path = "icons/evaluation_wizard.png";
        }
        else if (EVALUATION_WIZARD_KEY.equals(key)) {
           path = "icons/evaluation_wizard_KeY.png";
        }
        else if (EVALUATION_WIZARD_JAVA.equals(key)) {
           path = "icons/evaluation_wizard_Java.png";
        }
        else if (EMOTICON_FANTASY_DREAMING.equals(key)) {
           path = "icons/emoticons/fantasy_dreams.png";
        }
        else if (EMOTICON_FANTASY_DREAMING_ERROR.equals(key)) {
           return decorateImage(getImage(EMOTICON_FANTASY_DREAMING), FieldDecorationRegistry.getDefault().getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
        }
        else if (EMOTICON_OMG.equals(key)) {
           path = "icons/emoticons/omg.png";
        }
        else if (EMOTICON_OMG_ERROR.equals(key)) {
           return decorateImage(getImage(EMOTICON_OMG), FieldDecorationRegistry.getDefault().getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
        }
        else if (EMOTICON_WOW_DUDE.equals(key)) {
           path = "icons/emoticons/wow_dude.png";
        }
        else if (EMOTICON_WOW_DUDE_ERROR.equals(key)) {
           return decorateImage(getImage(EMOTICON_WOW_DUDE), FieldDecorationRegistry.getDefault().getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
        }
        else if (PIN_SHELL.equals(key)) {
           path = "icons/pin_view.gif";
        }
        else if (RESET_WORKBENCH.equals(key)) {
           path = "icons/resetWorkbench.gif";
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
     * Creates a new {@link Image} equal to the base {@link Image} on
     * which additional the decoration {@link Image} is drawn bottom right.
     * @param baseImage The base {@link Image}.
     * @param decorationImage The decoration {@link Image} to draw on base {@link Image}.
     * @return The new {@link Image}.
     */
    protected static Image decorateImage(Image baseImage, Image decorationImage) {
       ImageData decorationData = decorationImage.getImageData();
       // Create result image data
       ImageData resultData = baseImage.getImageData();
       // Make area on which decoration will be placed transparent
       int decX = resultData.width - decorationData.width;
       int decY = resultData.height - decorationData.height;
       for (int x = 0; x < decorationData.width; x++) {
          for (int y = 0; y < decorationData.height; y++) {
             resultData.setAlpha(decX + x, decY + y, decorationData.getAlpha(x, y));
             resultData.setPixel(decX + x, decY + y, resultData.transparentPixel);
          }
       }
       // Create result image
       Image result = new Image(baseImage.getDevice(), resultData);
       // Draw decoration image
       GC gc = new GC(result);
       gc.drawImage(baseImage, 0, 0);
       gc.drawImage(decorationImage, decX, decY);
       gc.dispose();
       return result;
    }
}