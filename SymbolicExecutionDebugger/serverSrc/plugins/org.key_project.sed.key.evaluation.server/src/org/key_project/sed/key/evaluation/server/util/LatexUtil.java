package org.key_project.sed.key.evaluation.server.util;

import java.util.Arrays;

import org.key_project.util.java.StringUtil;

/**
 * Provides utility methods to create latex files.
 * @author Martin Hentschel
 */
public final class LatexUtil {
   /**
    * The file extension of "tex" files with leading dot.
    */
   public static final String TEX_FILE_EXTENSION_WITH_DOT = ".tex";

   /**
    * Forbid instances.
    */
   private LatexUtil() {
   }
   
   /**
    * Creates a latex document showing the given data as boxplots.
    * @param allData Each {@code double[]} array will be printed as one boxplot.
    * @param labels The labels to show at each boxplot.
    * @param k The k-value used to compute the whiskers.
    * @return The created latex document.
    */
   public static String createLatexBoxPlot(double[][] allData, String[] labels, double k) {
      // Compute data for boxplot
      double[] median = new double[allData.length]; // The median values
      double[] lowerQuartiles = new double[allData.length]; // The lower quartiles
      double[] upperQuartiles = new double[allData.length]; // The upper quartiles
      double[] lowerWhiskers = new double[allData.length]; // The lower whiskers
      double[] upperWhiskers = new double[allData.length]; // The upper whiskers
      for (int i = 0; i < allData.length; i++) {
         // Create working copy
         double[] copy = new double[allData[i].length];
         System.arraycopy(allData[i], 0, copy, 0, allData[i].length);
         Arrays.sort(copy);
         // Compute median, quartiles and whiskers
         median[i] = medianValue(copy, copy.length / 2);
         int lowerQuartileIndex = copy.length / 4;
         lowerQuartiles[i] = medianValue(copy, lowerQuartileIndex);
         int upperQuartileIndex = copy.length - 1 - lowerQuartileIndex;
         upperQuartiles[i] = medianValue(copy, upperQuartileIndex);
         double d = upperQuartiles[i] - lowerQuartiles[i];
         lowerWhiskers[i] = lowerQuartiles[i] - (k * d);
         upperWhiskers[i] = upperQuartiles[i] + (k * d);
         // Truncate whiskers to nearest actual value
         lowerWhiskers[i] = trunkateDecreasing(lowerQuartileIndex, copy, lowerWhiskers[i]);
         upperWhiskers[i] = trunkateIncreasing(upperQuartileIndex, copy, upperWhiskers[i]);
      }
      // Create latex file
      StringBuffer sb = new StringBuffer();
      sb.append("\\documentclass{article}" + StringUtil.NEW_LINE);
      sb.append("\\usepackage{pgfplots}" + StringUtil.NEW_LINE);
      sb.append("\\pgfplotsset{compat=1.8}" + StringUtil.NEW_LINE);
      sb.append("\\usepgfplotslibrary{statistics}" + StringUtil.NEW_LINE);
      sb.append("\\begin{document}" + StringUtil.NEW_LINE);
      
      sb.append("\\begin{tikzpicture}" + StringUtil.NEW_LINE);
      sb.append("\\begin{axis}" + StringUtil.NEW_LINE);
      sb.append("[" + StringUtil.NEW_LINE);
      sb.append("ytick={");
      for (int i = 0; i < allData.length; i++) {
         if (i > 0) {
            sb.append(", ");
         }
         sb.append(i + 1);
      }
      sb.append("}," + StringUtil.NEW_LINE);
      sb.append("yticklabels={");
      for (int i = 0; i < allData.length; i++) {
         if (i > 0) {
            sb.append(", ");
         }
         sb.append(labels[i]);
      }
      sb.append("}," + StringUtil.NEW_LINE);
      sb.append("]" + StringUtil.NEW_LINE);
      for (int i = 0; i < allData.length; i++) {
         sb.append("\\addplot+[" + StringUtil.NEW_LINE);
         sb.append("boxplot prepared={median=" + median[i]
                   + ", upper quartile=" + upperQuartiles[i]
                   + ", lower quartile=" + lowerQuartiles[i]
                   + ", upper whisker=" + upperWhiskers[i]
                   + ", lower whisker=" + lowerWhiskers[i]
                   + "}," + StringUtil.NEW_LINE);
         sb.append("] coordinates {};" + StringUtil.NEW_LINE);
      }
      sb.append("\\end{axis}" + StringUtil.NEW_LINE);
      sb.append("\\end{tikzpicture}" + StringUtil.NEW_LINE);
      
      sb.append("\\end{document}" + StringUtil.NEW_LINE);
      return sb.toString();
   }
   
   /**
    * Utility method to access a median value.
    * @param data The data.
    * @param upperIndex The requested upper index.
    * @return The median value.
    */
   public static double medianValue(double[] data, int upperIndex) {
      if (data.length % 2 == 0) {
         return (data[upperIndex] + data[upperIndex - 1]) / 2;
      }
      else {
         return data[upperIndex];
      }
   }
   
   /**
    * Searches the nearest value to the given reference value in the array starting at the given index.
    * @param index The index to start search at.
    * @param array The array to search in.
    * @param reference The reference value to search its nearest occurrence in the array.
    * @return The nearest found value or the reference value if none was found.
    */
   public static double trunkateDecreasing(int index, double[] array, double reference) {
      double previousDifference = Double.MAX_VALUE;
      int indexWithNearestValue = -1;
      while (index >= 0) {
         double difference = array[index] - reference;
         if (difference < 0) {
            difference = difference * -1;
         }
         if (difference < previousDifference) {
            previousDifference = difference;
            indexWithNearestValue = index;
         }
         else if (difference < previousDifference) { // Continued in case of equal difference
            break;
         }
         index--;
      }
      if (indexWithNearestValue >= 0) {
         return array[indexWithNearestValue];
      }
      else {
         return reference;
      }
   }
   
   /**
    * Searches the nearest value to the given reference value in the array starting at the given index.
    * @param index The index to start search at.
    * @param array The array to search in.
    * @param reference The reference value to search its nearest occurrence in the array.
    * @return The nearest found value or the reference value if none was found.
    */
   public static double trunkateIncreasing(int index, double[] array, double reference) {
      double previousDifference = Double.MAX_VALUE;
      int indexWithNearestValue = -1;
      while (index < array.length) {
         double difference = array[index] - reference;
         if (difference < 0) {
            difference = difference * -1;
         }
         if (difference < previousDifference) {
            previousDifference = difference;
            indexWithNearestValue = index;
         }
         else if (difference < previousDifference) { // Continued in case of equal difference
            break;
         }
         index++;
      }
      if (indexWithNearestValue >= 0) {
         return array[indexWithNearestValue];
      }
      else {
         return reference;
      }
   }
}
