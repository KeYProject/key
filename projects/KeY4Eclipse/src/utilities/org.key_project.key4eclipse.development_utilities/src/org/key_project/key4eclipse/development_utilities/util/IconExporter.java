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

package org.key_project.key4eclipse.development_utilities.util;

import java.awt.Color;
import java.awt.image.BufferedImage;
import java.io.File;

import javax.imageio.ImageIO;
import javax.swing.Icon;
import javax.swing.ImageIcon;

import junit.framework.TestCase;

import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.ImageLoader;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.junit.Test;
import org.key_project.key4eclipse.development_utilities.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.swt.ImageUtil;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.gui.IconFactory;

/**
 * <p>
 * This JUnit plug-in test copies the KeY icons into the eclipse plug-ins.
 * </p>
 * <p>
 * <b>Attention: </b> Before execution the test {@link #PREFIX} has to be updated.
 * </p>
 * @author Martin Hentschel
 */
public class IconExporter extends TestCase {
   private static final String PREFIX = "D:/Forschung/GIT/KeY/";
   
   @Test
   public void testExportImage() throws Exception {
      // Common UI
      ImageData hole17Image = ImageUtil.convertToImageData(ImageUtil.toBufferedImage(IconFactory.keyHole(17, 17), -5, -2));
      Image decProofFileImage = new Image(Display.getDefault(), BundleUtil.openInputStream(Activator.PLUGIN_ID, "icons/DEC_PROOF_FILE.png"));
      //Image decKeYFileImage = new Image(Display.getDefault(), BundleUtil.openInputStream(Activator.PLUGIN_ID, "icons/DEC_KEY_FILE.png"));
      decorateImages(new IconToDecorate(hole17Image, decProofFileImage, 16, 16, 0, 0, "projects/KeY4Eclipse/src/plugins/org.key_project.key4eclipse.common.ui/icons/prooffile16.png")
                     //, new IconToDecorate(hole17Image, decKeYFileImage, 16, 16, 0, 0, "projects/KeY4Eclipse/src/plugins/org.key_project.key4eclipse.common.ui/icons/keyfile16.png")
                     );
      
      // KeY Resources
      ImageData baseImage = ImageUtil.convertToImageData(ImageUtil.toBufferedImage(IconFactory.keyHole(16, 16), -1, -1));
      
      Image infoImage = new Image(Display.getDefault(), BundleUtil.openInputStream(Activator.PLUGIN_ID, "icons/DEC_FIELD_INFO.png"));
      
      Image empty16Image = new Image(Display.getDefault(), BundleUtil.openInputStream(Activator.PLUGIN_ID, "icons/empty16.png"));

      decorateImages(//new IconToDecorate(hole17Image, empty16Image, 16, 16, 0, 0, "projects/KeY4Eclipse/src/plugins/org.key_project.key4eclipse.resources/icons/projectIcon.png"), // This icon requires to fill the hole manually in white
                     new IconToDecorate(baseImage, infoImage, 12, 14, -3, -2, "projects/KeY4Eclipse/src/plugins/org.key_project.key4eclipse.resources/icons/keyinfo12x14.png"),
                     new IconToDecorate(baseImage, PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_DEC_FIELD_WARNING), 12, 14, -3, -2, "projects/KeY4Eclipse/src/plugins/org.key_project.key4eclipse.resources/icons/keywarning12x14.png"),
                     new IconToDecorate(baseImage, PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_DEC_FIELD_ERROR), 12, 14, -3, -2, "projects/KeY4Eclipse/src/plugins/org.key_project.key4eclipse.resources/icons/keyerror12x14.png"));

      
      
      
      // KeY Resources UI
      Image decProofMetaFileImage = new Image(Display.getDefault(), BundleUtil.openInputStream(Activator.PLUGIN_ID, "icons/DEC_PROOF_META_FILE.png"));
      decorateImages(new IconToDecorate(hole17Image, decProofMetaFileImage, 16, 16, 0, 0, "projects/KeY4Eclipse/src/plugins/org.key_project.key4eclipse.resources.ui/icons/proofmetafile16.png"));
      
      // KeY IDE
      treatIconsToExport(new IconToExpoert(IconFactory.keyHole(16, 16), -1, -1, "projects/KeYIDE/src/plugins/org.key_project.keyide.ui/icons/ekey-mono16.png"),
                         new IconToExpoert(new IconFactory.KeYFolderIcon(Color.GRAY), "projects/KeYIDE/src/plugins/org.key_project.keyide.ui/icons/folder16.png"),
                         new IconToExpoert(IconFactory.provedFolderIcon(), "projects/KeYIDE/src/plugins/org.key_project.keyide.ui/icons/folderproved16.png"),
                         new IconToExpoert(IconFactory.keyHoleClosed(16, 16), -1, -1, "projects/KeYIDE/src/plugins/org.key_project.keyide.ui/icons/keyproved16.png"),
                         new IconToExpoert(IconFactory.interactiveAppLogo(16), "projects/KeYIDE/src/plugins/org.key_project.keyide.ui/icons/interactiveAppLogo16.png"),
                         new IconToExpoert(IconFactory.pruneLogo(16), "projects/KeYIDE/src/plugins/org.key_project.keyide.ui/icons/prune16.png"));
      decorateImages(new IconToDecorate(hole17Image, decProofFileImage, 16, 16, 0, 0, "projects/KeYIDE/src/plugins/org.key_project.keyide.ui/icons/prooffile16.png"));
   }
   
   private void decorateImages(IconToDecorate... tasks) {
      for (IconToDecorate task : tasks) {
         Image decorationImage = task.getDecoration();

         ImageData baseData = task.getBaseImage();
         Image baseImage = new Image(Display.getDefault(), baseData);
         
         Image result = new Image(Display.getDefault(), task.getWidth(), task.getHeight());
         
         GC gc = new GC(result);
         gc.drawImage(baseImage, task.getBaseX(), task.getBaseY());
         int decX = task.getDecX() != null ?
                    task.getDecX() :
                    result.getBounds().width - decorationImage.getBounds().width;
         int decY = task.getDecY() != null ?
                    task.getDecY() :
                       result.getBounds().height - decorationImage.getBounds().height;
         gc.drawImage(decorationImage, decX, decY);
         gc.dispose();
    
         ImageData resultData = result.getImageData();
         int whitePixel = resultData.palette.getPixel(new RGB(255,255,255));
         resultData.transparentPixel = whitePixel;
         
         ImageLoader imageLoader = new ImageLoader();
         imageLoader.data = new ImageData[] {resultData};
         imageLoader.save(PREFIX + task.getTarget(), SWT.IMAGE_PNG);
         System.out.println("Saved: " + PREFIX + task.getTarget());
      }
   }
   
   private static class IconToDecorate {
      private final ImageData baseImage;

      private final Image decoration;
      
      private final int width;
      
      private final int height;
      
      private final int baseX;
      
      private final int baseY;
      
      private final Integer decX;
      
      private final Integer decY;
      
      private final String target;

      public IconToDecorate(ImageData baseImage, Image decoration, int width, int height, int baseX, int baseY, String target) {
         this(baseImage, decoration, width, height, baseX, baseY, null, null, target);
      }

      public IconToDecorate(ImageData baseImage, Image decoration, int width, int height, int baseX, int baseY, Integer decX, Integer decY, String target) {
         this.baseImage = baseImage;
         this.decoration = decoration;
         this.width = width;
         this.height = height;
         this.baseX = baseX;
         this.baseY = baseY;
         this.decX = decX;
         this.decY = decY;
         this.target = target;
      }

      public String getTarget() {
         return target;
      }

      public int getBaseX() {
         return baseX;
      }

      public int getBaseY() {
         return baseY;
      }

      public Integer getDecX() {
         return decX;
      }

      public Integer getDecY() {
         return decY;
      }

      public int getWidth() {
         return width;
      }

      public int getHeight() {
         return height;
      }

      public ImageData getBaseImage() {
         return baseImage;
      }

      public Image getDecoration() {
         return decoration;
      }
   }
   
   private void treatIconsToExport(IconToExpoert... tasks) {
      try {
         for (IconToExpoert task : tasks) {
            BufferedImage bi = task.getImage() != null ?
                               ImageUtil.toBufferedImage(task.getImage().getImage(), task.getX(), task.getY()) :
                               ImageUtil.toBufferedImage(task.getIcon(), task.getX(), task.getY());
            for (String target : task.getTargets()) {
               File targetFile = new File(PREFIX + target);
               ImageIO.write(bi, IOUtil.getFileExtension(targetFile), targetFile);
               System.out.println("Saved: " + targetFile);
            }
         }
     }
     catch (Exception e) {
        e.printStackTrace();
     }
   }
   
   private static class IconToExpoert {
      private final ImageIcon image;
      
      private final Icon icon;
      
      private final String[] targets;
      
      private final int x;
      
      private final int y;

      public IconToExpoert(Icon icon, String... targets) {
         this(icon, 0, 0, targets);
      }

      public IconToExpoert(Icon icon, int x, int y, String... targets) {
         this.image = null;
         this.icon = icon;
         this.x = x;
         this.y = y;
         this.targets = targets;
      }

      public IconToExpoert(ImageIcon image, String... targets) {
         this(image, 0, 0, targets);
      }

      public IconToExpoert(ImageIcon image, int x, int y, String... targets) {
         this.image = image;
         this.icon = null;
         this.x = x;
         this.y = y;
         this.targets = targets;
      }

      public Icon getIcon() {
         return icon;
      }

      public ImageIcon getImage() {
         return image;
      }

      public int getX() {
         return x;
      }

      public int getY() {
         return y;
      }

      public String[] getTargets() {
         return targets;
      }
   }
}