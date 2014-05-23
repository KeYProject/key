package org.key_project.util.java;

import org.eclipse.swt.graphics.RGB;

/**
 * Provides static methods to work with colors.
 * @author Martin Hentschel
 */
public class ColorUtil {
   /**
    * Forbid instances.
    */
   private ColorUtil() {
   }
   
   /**
    * Converts the given {@link RGB} into a hex string.
    * @param rgb The {@link RGB} to convert.
    * @return The hex values.
    */
   public static String toHexRGBString(RGB rgb) {
      return toHexRGBString(rgb.red, rgb.green, rgb.blue);
   }
   
   /**
    * Converts the given red, green and blue value into a hex string.
    * @param red The red value.
    * @param green The green value.
    * @param blue The blue value.
    * @return The hex values.
    */
   public static String toHexRGBString(int red, int green, int blue) {
      String redString = Integer.toHexString(red);
      String greenString = Integer.toHexString(green);
      String blueString = Integer.toHexString(blue);
      if (redString.length() == 1) {
         redString = "0" + redString;
      }
      if (greenString.length() == 1) {
         greenString = "0" + greenString;
      }
      if (blueString.length() == 1) {
         blueString = "0" + blueString;
      }
      return redString.toUpperCase() + greenString.toUpperCase() + blueString.toUpperCase();
   }
   
   /**
    * Scales the brightness of the given {@link RGB}.
    * @param rgb The {@link RGB} to scale its brightness.
    * @param factor The scale factor.
    * @return The scaled {@link RGB} value.
    */
   public static RGB scaleBrightness(RGB rgb, float factor) {
      return scaleBrightness(rgb.red, rgb.green, rgb.blue, factor);
   }
   
   /**
    * Scales the brightness of the color defined by the red, green and blue value.
    * @param red The red value.
    * @param green The green value.
    * @param blue The blue value.
    * @param factor The scale factor.
    * @return The scaled {@link RGB} value.
    */
   public static RGB scaleBrightness(int red, int green, int blue, float factor) {
      float[] model = normalize(red, green, blue);
      RGBtoHSL(model, model);
      model[2] = model[2] * factor;
      HSLtoRGB(model, model);
      return new RGB(to8bit(model[0]), to8bit(model[1]), to8bit(model[2]));
   }
   
   /**
    * Normalizes the red, green and blue values.
    * @param red The red value.
    * @param green The green value.
    * @param blue The blue value.
    * @return The normalized red, green and blue values.
    */
   public static float[] normalize(int red, int green, int blue) {
      float[] result = new float[3];
      result[0] = normalize(red);
      result[1] = normalize(green);
      result[2] = normalize(blue);
      return result;
   }

   /**
    * This method was copied from class {@code javax.swing.colorchooser.ColorModel} of Java 7.
    */
   private static float normalize(int value) {
       return (float) (value & 0xFF) / 255.0f;
   }

   /**
    * <p>
    * Converts RGB components of a color to a set of HSL components.
    * </p>
    * <p>
    * This method was copied from class {@code javax.swing.colorchooser.ColorModelHSL} of Java 7.
    * </p>
    *
    * @param rgb  a float array with length of at least 3
    *             that contains RGB components of a color
    * @param hsl  a float array with length equal to
    *             the number of HSL components
    * @return a float array that contains HSL components
    */
   public static float[] RGBtoHSL(float[] rgb, float[] hsl) {
       if (hsl == null) {
           hsl = new float[3];
       }
       float max = max(rgb[0], rgb[1], rgb[2]);
       float min = min(rgb[0], rgb[1], rgb[2]);

       float summa = max + min;
       float saturation = max - min;
       if (saturation > 0.0f) {
           saturation /= (summa > 1.0f)
                   ? 2.0f - summa
                   : summa;
       }
       hsl[0] = getHue(rgb[0], rgb[1], rgb[2], max, min);
       hsl[1] = saturation;
       hsl[2] = summa / 2.0f;
       return hsl;
   }

   /**
    * <p>
    * Calculates the hue component for HSL and HSV color spaces.
    * </p>
    * <p>
    * This method was copied from class {@code javax.swing.colorchooser.ColorModelHSL} of Java 7.
    * </p>
    *
    * @param red    the red component of the color
    * @param green  the green component of the color
    * @param blue   the blue component of the color
    * @param max    the larger of {@code red}, {@code green} and {@code blue}
    * @param min    the smaller of {@code red}, {@code green} and {@code blue}
    * @return the hue component
    */
   private static float getHue(float red, float green, float blue, float max, float min) {
       float hue = max - min;
       if (hue > 0.0f) {
           if (max == red) {
               hue = (green - blue) / hue;
               if (hue < 0.0f) {
                   hue += 6.0f;
               }
           }
           else if (max == green) {
               hue = 2.0f + (blue - red) / hue;
           }
           else /*max == blue*/ {
               hue = 4.0f + (red - green) / hue;
           }
           hue /= 6.0f;
       }
       return hue;
   }

  /**
   * <p>
   * Converts HSL components of a color to a set of RGB components.
   * </p>
   * <p>
   * This method was copied from class {@code javax.swing.colorchooser.ColorModelHSL} of Java 7.
   * </p>
   *
   * @param hsl  a float array with length equal to
   *             the number of HSL components
   * @param rgb  a float array with length of at least 3
   *             that contains RGB components of a color
   * @return a float array that contains RGB components
   */
  public static float[] HSLtoRGB(float[] hsl, float[] rgb) {
      if (rgb == null) {
          rgb = new float[3];
      }
      float hue = hsl[0];
      float saturation = hsl[1];
      float lightness = hsl[2];

      if (saturation > 0.0f) {
          hue = (hue < 1.0f) ? hue * 6.0f : 0.0f;
          float q = lightness + saturation * ((lightness > 0.5f) ? 1.0f - lightness : lightness);
          float p = 2.0f * lightness - q;
          rgb[0]= normalize(q, p, (hue < 4.0f) ? (hue + 2.0f) : (hue - 4.0f));
          rgb[1]= normalize(q, p, hue);
          rgb[2]= normalize(q, p, (hue < 2.0f) ? (hue + 4.0f) : (hue - 2.0f));
      }
      else {
          rgb[0] = lightness;
          rgb[1] = lightness;
          rgb[2] = lightness;
      }
      return rgb;
  }
  
  /**
   *  This method was copied from class {@code javax.swing.colorchooser.ColorModel} of Java 7.
   */
  private static int to8bit(float value) {
     return (int) (255.0f * value);
  }

  /**
   * <p>
   * Returns the smaller of three color components.
   * </p>
   * <p>
   * This method was copied from class {@code javax.swing.colorchooser.ColorModelHSL} of Java 7.
   * </p>
   *
   * @param red    the red component of the color
   * @param green  the green component of the color
   * @param blue   the blue component of the color
   * @return the smaller of {@code red}, {@code green} and {@code blue}
   */
  private static float min(float red, float green, float blue) {
      float min = (red < green) ? red : green;
      return (min < blue) ? min : blue;
  }

  /**
   * <p>
   * Returns the larger of three color components.
   * </p>
   * <p>
   * This method was copied from class {@code javax.swing.colorchooser.ColorModelHSL} of Java 7.
   * </p>
   *
   * @param red    the red component of the color
   * @param green  the green component of the color
   * @param blue   the blue component of the color
   * @return the larger of {@code red}, {@code green} and {@code blue}
   */
  private static float max(float red, float green, float blue) {
      float max = (red > green) ? red : green;
      return (max > blue) ? max : blue;
  }

  /**
   * This method was copied from class {@code javax.swing.colorchooser.ColorModelHSL} of Java 7.
   */
  private static float normalize(float q, float p, float color) {
      if (color < 1.0f) {
          return p + (q - p) * color;
      }
      if (color < 3.0f) {
          return q;
      }
      if (color < 4.0f) {
          return p + (q - p) * (4.0f - color);
      }
      return p;
   }
}
