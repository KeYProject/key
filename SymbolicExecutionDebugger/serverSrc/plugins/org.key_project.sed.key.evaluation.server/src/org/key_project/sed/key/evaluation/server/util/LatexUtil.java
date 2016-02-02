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
    * @param yLabels The y labels to show at each boxplot.
    * @param xLabel The x label to show at the overall boxplot.
    * @param k The k-value used to compute the whiskers.
    * @param reverseOrder Reverse order of box plots?
    * @return The created latex document.
    */
   public static String createLatexBoxPlot(double[][] allData, 
                                           String[] yLabels, 
                                           String xLabel, 
                                           double k, 
                                           boolean reverseOrder,
                                           int xMin,
                                           int xMax) {
      // Change order if reverse order is requested.
      if (reverseOrder) {
         double[][] allDataReverse = new double[allData.length][];
         for (int i = 0; i < allData.length; i++) {
            allDataReverse[allDataReverse.length - 1 - i] = allData[i];
         }
         allData = allDataReverse;
         String[] yLabelsReverse = new String[yLabels.length];
         for (int i = 0; i < yLabels.length; i++) {
            yLabelsReverse[yLabelsReverse.length - 1 - i] = yLabels[i];
         }
         yLabels = yLabelsReverse;
      }
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
      // preamble
      sb.append("%\\documentclass{article}" + StringUtil.NEW_LINE);
      sb.append("%\\usepackage{pgfplots}" + StringUtil.NEW_LINE);
      sb.append("%\\pgfplotsset{compat=1.12} % Ensures correct results!" + StringUtil.NEW_LINE);
      sb.append("%\\usepgfplotslibrary{statistics}" + StringUtil.NEW_LINE);
      sb.append("%\\begin{document}" + StringUtil.NEW_LINE);
      // preset boxplot
      sb.append("%\\begin{tikzpicture}" + StringUtil.NEW_LINE);
      sb.append("%\\begin{axis}" + StringUtil.NEW_LINE);
      sb.append("%[" + StringUtil.NEW_LINE);
      if (!StringUtil.isEmpty(xLabel)) {
         sb.append("%xlabel={" + xLabel + "}," + StringUtil.NEW_LINE);
      }
      sb.append("%ytick={");
      for (int i = 0; i < allData.length; i++) {
         if (i > 0) {
            sb.append(", ");
         }
         sb.append(i + 1);
      }
      sb.append("%}," + StringUtil.NEW_LINE);
      sb.append("%yticklabels={");
      for (int i = 0; i < allData.length; i++) {
         if (i > 0) {
            sb.append(", ");
         }
         sb.append(yLabels[i]);
      }
      sb.append("%}," + StringUtil.NEW_LINE);
      sb.append("%y=1cm," + StringUtil.NEW_LINE);
      sb.append("%xmin=" + xMin + "," + StringUtil.NEW_LINE);
      sb.append("%xmax=" + xMax + "," + StringUtil.NEW_LINE);
      sb.append("%]" + StringUtil.NEW_LINE);
      for (int i = 0; i < allData.length; i++) {
         sb.append("%\\addplot+[" + StringUtil.NEW_LINE);
         sb.append("%boxplot prepared={median=" + median[i]
                   + ", upper quartile=" + upperQuartiles[i]
                   + ", lower quartile=" + lowerQuartiles[i]
                   + ", upper whisker=" + upperWhiskers[i]
                   + ", lower whisker=" + lowerWhiskers[i]
                   + "}," + StringUtil.NEW_LINE);
         sb.append("%] coordinates {};" + StringUtil.NEW_LINE);
      }
      sb.append("%\\end{axis}" + StringUtil.NEW_LINE);
      sb.append("%\\end{tikzpicture}" + StringUtil.NEW_LINE);
      // auto computed boxplot
      sb.append(StringUtil.NEW_LINE + StringUtil.NEW_LINE);
      sb.append("\\begin{tikzpicture}" + StringUtil.NEW_LINE);
      sb.append("\\begin{axis}" + StringUtil.NEW_LINE);
      sb.append("[" + StringUtil.NEW_LINE);
      if (!StringUtil.isEmpty(xLabel)) {
         sb.append("xlabel={" + xLabel + "}," + StringUtil.NEW_LINE);
      }
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
         sb.append(yLabels[i]);
      }
      sb.append("}," + StringUtil.NEW_LINE);
      sb.append("y=1cm," + StringUtil.NEW_LINE);
      sb.append("xmin=" + xMin + "," + StringUtil.NEW_LINE);
      sb.append("xmax=" + xMax + "," + StringUtil.NEW_LINE);
      sb.append("]" + StringUtil.NEW_LINE);
      for (int i = 0; i < allData.length; i++) {
         sb.append("\\addplot+[boxplot={}] " + StringUtil.NEW_LINE);
         sb.append("table[row sep=\\\\,y index=0] {data \\\\");
         for (int j = 0; j < allData[i].length; j++) {
            if (j > 0) {
               sb.append(" ");
            }
            sb.append(allData[i][j] + " \\\\");
         }
         sb.append("};");
         sb.append("coordinates {};" + StringUtil.NEW_LINE);
      }
      sb.append("\\end{axis}" + StringUtil.NEW_LINE);
      sb.append("\\end{tikzpicture}" + StringUtil.NEW_LINE);
      // end of document
      sb.append("%\\end{document}" + StringUtil.NEW_LINE);
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
    * @return The nearest found value not exceeding the reference or the reference value if none was found.
    */
   public static double trunkateDecreasing(int index, double[] array, double reference) {
      double previousDifference = Double.MAX_VALUE;
      int indexWithNearestValue = -1;
      boolean previousInitialzed = false;
      while (index >= 0) {
         double difference = array[index] - reference;
         if (difference < 0) {
            break; // Outliners reached
         }
         else if (!previousInitialzed) {
            previousDifference = difference;
            indexWithNearestValue = index;
            previousInitialzed = true;
         }
         else if (difference < previousDifference) {
            previousDifference = difference;
            indexWithNearestValue = index;
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
    * @return The nearest found value not exceeding the reference or the reference value if none was found.
    */
   public static double trunkateIncreasing(int index, double[] array, double reference) {
      double previousDifference = Double.MIN_VALUE;
      int indexWithNearestValue = -1;
      boolean previousInitialzed = false;
      while (index < array.length) {
         double difference = array[index] - reference;
         if (difference > 0) {
            break; // Outliners reached
         }
         else if (!previousInitialzed) {
            previousDifference = difference;
            indexWithNearestValue = index;
            previousInitialzed = true;
         }
         else if (previousDifference < difference) {
            previousDifference = difference;
            indexWithNearestValue = index;
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
