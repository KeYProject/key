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

package org.key_project.util.eclipse.swt;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Image;
import java.awt.Toolkit;
import java.awt.Transparency;
import java.awt.image.BufferedImage;
import java.awt.image.DirectColorModel;
import java.awt.image.FilteredImageSource;
import java.awt.image.ImageFilter;
import java.awt.image.ImageProducer;
import java.awt.image.IndexColorModel;
import java.awt.image.RGBImageFilter;
import java.awt.image.WritableRaster;

import javax.swing.Icon;
import javax.swing.JEditorPane;
import javax.swing.JFrame;
import javax.swing.text.Document;
import javax.swing.text.html.HTMLDocument;
import javax.swing.text.html.HTMLEditorKit;
import javax.swing.text.html.StyleSheet;

import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.PaletteData;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

/**
 * Provides static methods to work with images.
 * @author Martin Hentschel
 */
public final class ImageUtil {
    /**
     * Forbid instances.
     */
    private ImageUtil() {
    }
    
    /**
     * <p>
     * Renders the given HTML text as image.
     * </p>
     * <p>
     * Fore more details about changing the default font ofa JEditorPane have a look at
     * <a href="http://explodingpixels.wordpress.com/2008/10/28/make-jeditorpane-use-the-system-font/">http://explodingpixels.wordpress.com/2008/10/28/make-jeditorpane-use-the-system-font/</a>.
     * </p>
     * @param html The HTML text to render.
     * @param useDefaultSystemFont Use SWT system font as default?
     * @param transparentBackground Use transparent background color?
     * @return The created image that shows the HTML content.
     */
    public static BufferedImage renderHTML(String html, boolean useDefaultSystemFont, boolean transparentBackground) {
        // Use a JEditorPane to render the HTML text.
        JEditorPane pane = new JEditorPane();
        // Modify pane to use default system font
        try {
            pane.setContentType(new HTMLEditorKit().getContentType());
            if (useDefaultSystemFont) {
                Font font = Display.getDefault().getSystemFont();
                if (font != null && font.getFontData().length >= 1) {
                    FontData data = font.getFontData()[0];
                    String bodyRule = "body { font-family: " + data.getName() + "; }";
                    Document document = pane.getDocument();
                    if (document instanceof HTMLDocument) {
                        StyleSheet sheet = ((HTMLDocument)document).getStyleSheet();
                        sheet.addRule(bodyRule);
                    }
                }
            }
            pane.setText(html);
        }
        catch (Exception e) {
            e.printStackTrace();
        }
        // Put the JEditorPane into a JFrame to optimize the width and height.
        JFrame frame = new JFrame();
        frame.setLayout(new BorderLayout());
        frame.add(pane, BorderLayout.CENTER);
        frame.pack();
        // Create screenshot of JEditorPane.
        BufferedImage image = new BufferedImage(pane.getWidth(), pane.getHeight(), BufferedImage.TYPE_INT_ARGB);
        Graphics g = image.getGraphics();
        try {
            pane.paint(g);
        }
        finally {
            g.dispose();
        }
        if (transparentBackground) {
            // Make background transparent if required.
            final Color transparentColor = pane.getBackground();
            java.awt.Image transparentImage = ImageUtil.makeColorTransparent(image, transparentColor);
            return ImageUtil.toBufferedImage(transparentImage);
        }
        else {
            return image;
        }
    }
    
    /**
     * <p>
     * Makes the given color in the given {@link Image} transparent.
     * </p>
     * <p>
     * Fore more details have a look at
     * <a href="http://stackoverflow.com/questions/665406/how-to-make-a-color-transparent-in-a-bufferedimage-and-save-as-png">http://stackoverflow.com/questions/665406/how-to-make-a-color-transparent-in-a-bufferedimage-and-save-as-png</a>.
     * </p>
     * @param image The {@link Image} to modify.
     * @param transparentColor The color to make transparent.
     * @return A new created {@link Image} where the color is transparent.
     */
    public static Image makeColorTransparent(Image image,
                                             final Color transparentColor) {
        ImageFilter filter = new RGBImageFilter() {
            @Override
            public final int filterRGB(int x, int y, int rgb) {
                if (rgb == transparentColor.getRGB()) {
                    return rgb & 0xFFFFFF; // Set fully transparent but keep color
                }
                return rgb;
            }
        };
        ImageProducer ip = new FilteredImageSource(image.getSource(), filter);
        return Toolkit.getDefaultToolkit().createImage(ip);
    }
    
    /**
     * Converts the given {@link Image} into a {@link BufferedImage}.
     * @param image The {@link Image} to convert.
     * @return The created {@link BufferedImage} with the content from the given {@link Image}.
     */
    public static BufferedImage toBufferedImage(Image image) {
        BufferedImage result = new BufferedImage(image.getWidth(null), 
                                                 image.getHeight(null), 
                                                 BufferedImage.TYPE_INT_ARGB);
        Graphics g = result.getGraphics();
        try {
            g.drawImage(image, 0, 0, null);
            return result;
        }
        finally {
            g.dispose();
        }
    }
    
    /**
     * <p>
     * Converts the given {@link Icon} into a {@link BufferedImage}.
     * </p>
     * <p>
     * Fore more details have a look at
     * <a href="http://www.java2s.com/Tutorial/Java/0280__SWT/ConvertsanAWTimagetoSWT.htm">http://www.java2s.com/Tutorial/Java/0280__SWT/ConvertsanAWTimagetoSWT.htm</a>.
     * </p>
     * @param icon The {@link Icon} to convert.
     * @return The created {@link BufferedImage}.
     */
    public static BufferedImage toBufferedImage(Icon icon) {
        if (icon != null) {
            Graphics2D g = null;
            try {
                BufferedImage image = new BufferedImage(icon.getIconWidth(), icon.getIconHeight(), Transparency.TRANSLUCENT);
                g = image.createGraphics();
                icon.paintIcon(null, g, 0, 0);
                return image;
            }
            finally {
                if (g != null) {
                    g.dispose();
                }
            }
        }
        else {
            return null;
        }
    }
    
    /**
     * <p>
     * Converts the {@link BufferedImage} from AWT into {@link ImageData}
     * for SWT.
     * </p>
     * <p>
     * For more details have a look at
     * <a href="http://code.google.com/p/beanfabrics/source/browse/trunk/beanfabrics/beanfabrics-swt-samples/src/main/java/org/beanfabrics/swt/samples/filebrowser/ImageConverter.java?r=498">http://code.google.com/p/beanfabrics/source/browse/trunk/beanfabrics/beanfabrics-swt-samples/src/main/java/org/beanfabrics/swt/samples/filebrowser/ImageConverter.java?r=498</a>.
     * </p>
     * @param bufferedImage The {@link BufferedImage} to convert.
     * @return The {@link ImageData} for SWT.
     */
    public static ImageData convertToImageData(BufferedImage bufferedImage) {
        if (bufferedImage.getColorModel() instanceof DirectColorModel) {
            DirectColorModel colorModel = (DirectColorModel) bufferedImage.getColorModel();
            PaletteData palette = new PaletteData(colorModel.getRedMask(), colorModel.getGreenMask(), colorModel.getBlueMask());

            ImageData data = new ImageData(bufferedImage.getWidth(), bufferedImage.getHeight(), colorModel.getPixelSize(), palette);
            data.alphaData = new byte[bufferedImage.getWidth() * bufferedImage.getHeight()];

            WritableRaster alphaRaster = bufferedImage.getAlphaRaster();
            for (int y = 0; y < data.height; y++) {
                for (int x = 0; x < data.width; x++) {
                    int rgb = bufferedImage.getRGB(x, y);
                    int alpha = alphaRaster.getSample(x, y, 0);
                    data.alphaData[y * data.width + x] = (byte) alpha;
                    int pixel = palette.getPixel(new RGB((rgb >> 16) & 0xFF, (rgb >> 8) & 0xFF, rgb & 0xFF));
                    data.setPixel(x, y, pixel);
                }
            }

            return data;
        }
        else if (bufferedImage.getColorModel() instanceof IndexColorModel) {
            IndexColorModel colorModel = (IndexColorModel) bufferedImage.getColorModel();
            int size = colorModel.getMapSize();
            byte[] reds = new byte[size];
            byte[] greens = new byte[size];
            byte[] blues = new byte[size];
            colorModel.getReds(reds);
            colorModel.getGreens(greens);
            colorModel.getBlues(blues);
            RGB[] rgbs = new RGB[size];
            for (int i = 0; i < rgbs.length; i++) {
                rgbs[i] = new RGB(reds[i] & 0xFF, greens[i] & 0xFF, blues[i] & 0xFF);
            }
            PaletteData palette = new PaletteData(rgbs);
            ImageData data = new ImageData(bufferedImage.getWidth(), bufferedImage.getHeight(), colorModel.getPixelSize(), palette);
            data.transparentPixel = colorModel.getTransparentPixel();
            WritableRaster raster = bufferedImage.getRaster();
            int[] pixelArray = new int[1];
            for (int y = 0; y < data.height; y++) {
                for (int x = 0; x < data.width; x++) {
                    raster.getPixel(x, y, pixelArray);
                    data.setPixel(x, y, pixelArray[0]);
                }
            }
            return data;
        }
        return null;
    }
}