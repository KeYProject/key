package org.key_project.key4eclipse.util.eclipse.swt;

import java.awt.Graphics2D;
import java.awt.Transparency;
import java.awt.image.BufferedImage;
import java.awt.image.DirectColorModel;
import java.awt.image.IndexColorModel;
import java.awt.image.WritableRaster;

import javax.swing.Icon;

import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.PaletteData;
import org.eclipse.swt.graphics.RGB;

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
