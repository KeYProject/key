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

package org.key_project.monkey.product.ui.batch;

import java.io.File;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.key_project.monkey.product.ui.util.MonKeYUtil;
import org.key_project.util.java.StringUtil;

/**
 * Represents the parameters of {@link MonKeYBatchMode}.
 * @author Martin Hentschel
 * @see MonKeYBatchApplication.
 */
public class MonKeYBatchModeParameters {
   /**
    * Parameter for {@link #showHelp}.
    */
   public static final String PARAM_SHOW_HELP = "-h";
   
   /**
    * Parameter for {@link #mainWindowOff}.
    */
   public static final String PARAM_MAIN_WINDOW_OFF = "-nowindow";
   
   /**
    * Parameter for {@link #methodTreatmentContract}.
    */
   public static final String PARAM_METHOD_TREATMENT_CONTRACT = "-mtcontract";
   
   /**
    * Parameter for {@link #dependencyContractsOff}.
    */
   public static final String PARAM_DEPENDENCY_CONTRACTS_OFF = "-dcoff";
   
   /**
    * Parameter for {@link #queryTreatmentOff}.
    */
   public static final String PARAM_QUERY_TREATMENT_OFF = "-qtoff";
   
   /**
    * Parameter for {@link #arithmeticTreatmentBase}.
    */
   public static final String PARAM_ARITHMETIC_TREATMENT_BASE = "-atbase";
   
   /**
    * Parameter for {@link #stopAtUnclosable}.
    */
   public static final String PARAM_STOP_AT_UNCLOSABLE = "-stopAtUnclosable";
   
   /**
    * Parameter for {@link #bootClassPath}.
    */
   public static final String PARAM_BOOT_CLASS_PATH = "-bc";
   
   /**
    * Parameter for {@link #dummyLoadOff}.
    */
   public static final String PARAM_DUMMY_LOAD_OFF = "-dloff";
   
   /**
    * Parameter for {@link #outputPath}.
    */
   public static final String PARAM_OUTPUT_PATH = "-out";
   
   /**
    * Parameter for {@link #numberOfRoundsText}.
    */
   public static final String PARAM_ROUNDS = "-rounds";
   
   /**
    * Parameter for {@link #getLocationLoadDirectory(int)}.
    */
   public static final String PARAM_LOAD_PREFIX = "-load";
   
   /**
    * Parameter for {@link #maxRuleApplications}.
    */
   public static final String PARAM_MAX_RULES = "-maxRules";
   
   /**
    * Show help?
    */
   private boolean showHelp;
   
   /**
    * Do not show main window?
    */
   private boolean mainWindowOff;
   
   /**
    * Use method treatment contracts instead of expand?
    */
   private boolean methodTreatmentContract;
   
   /**
    * Use dependency contracts off instead of on?
    */
   private boolean dependencyContractsOff;
   
   /**
    * Use query treatment off instead of on?
    */
   private boolean queryTreatmentOff;
   
   /**
    * Use arithmetic treatment base instead of defOps?
    */
   private boolean arithmeticTreatmentBase;
   
   /**
    * Stop at unclosable?
    */
   private boolean stopAtUnclosable;
   
   /**
    * Do not load the first location twice to filter out API parsing time. 
    */
   private boolean dummyLoadOff;

   /**
    * Boot class path to use or {@code null} to use default boot class path.
    */
   private String bootClassPath;
   
   /**
    * Output path.
    */
   private String outputPath;
   
   /**
    * The maximal number of rule applications;
    */
   private int maxRuleApplications = MonKeYUtil.DEFAULT_MAX_RULE_APPLICATIONS;
   
   /**
    * Source locations.
    */
   private List<String> locations = new LinkedList<String>();
   
   /**
    * The unparsed number of rounds.
    */
   private String numberOfRoundsText;
   
   /**
    * Maps the index of a location of {@link #locations} to a directory which provide proof files to load.
    */
   private Map<Integer, String> locationLoadDirectories = new HashMap<Integer, String>();
   
   /**
    * Checks if help should be shown.
    * @return Show help?
    */
   public boolean isShowHelp() {
      return showHelp;
   }
   
   /**
    * Checks if no main window should be shown.
    * @return Do not show main window?
    */
   public boolean isMainWindowOff() {
      return mainWindowOff;
   }
   
   /**
    * Checks if method treatment contracts should be used instead of expand?
    * @return Use method treatment contracts instead of expand?
    */
   public boolean isMethodTreatmentContract() {
      return methodTreatmentContract;
   }
   
   /**
    * Checks if dependency contracts off should be used instead of on?
    * @return Use dependency contracts off instead of on?
    */
   public boolean isDependencyContractsOff() {
      return dependencyContractsOff;
   }
   
   /**
    * Checks if query treatment off should be used instead of on?
    * @return Use query treatment off instead of on?
    */
   public boolean isQueryTreatmentOff() {
      return queryTreatmentOff;
   }
   
   /**
    * Checks if arithmetic treatment base should be used instead of defOps?
    * @return Use arithmetic treatment base instead of defOps?
    */
   public boolean isArithmeticTreatmentBase() {
      return arithmeticTreatmentBase;
   }
   
   /**
    * Checks if proof search stops at first unclosable goal.
    * @return Stop at first unclosable goal?
    */
   public boolean isStopAtUnclosable() {
      return stopAtUnclosable;
   }

   /**
    * Returns the maximal number of rule applications.
    * @return The maximal number of rule applications.
    */
   public int getMaxRuleApplications() {
      return maxRuleApplications;
   }

   /**
    * Returns the boot class path to use or {@code null} to use default boot class path.
    * @return The boot class path to use or {@code null} to use default boot class path.
    */
   public String getBootClassPath() {
      return bootClassPath;
   }
   
   /**
    * Checks if the first location should not be loaded twice to filter out API parsing time. 
    * @return Do not load the first location twice to filter out API parsing time. 
    */
   public boolean isDummyLoadOff() {
      return dummyLoadOff;
   }
   
   /**
    * Returns the output path.
    * @return The output path.
    */
   public String getOutputPath() {
      return outputPath;
   }
   
   /**
    * Returns the source locations.
    * @return The source locations.
    */
   public List<String> getLocations() {
      return locations;
   }
   
   /**
    * Returns the unparsed number of rounds.
    * @return The unparsed number of rounds.
    */
   protected String getNumberOfRoundsText() {
      return numberOfRoundsText;
   }
   
   /**
    * Returns the number of rounds.
    * @return The number of rounds.
    */
   public int getNumberOfRounds() {
      if (!StringUtil.isTrimmedEmpty(getNumberOfRoundsText())) {
         return Integer.valueOf(getNumberOfRoundsText());
      }
      else {
         return 1;
      }
   }

   /**
    * Checks if the number of rounds {@link #getNumberOfRounds()} is valid.
    * @return {@code true} valid, {@code false} invalid.
    */
   protected boolean isNumberOfRoundsValid() {
      try {
         int number = getNumberOfRounds();
         return number >= 1;
      }
      catch (Exception e) {
         return false;
      }
   }
   
   /**
    * Checks if the parameters are valid.
    * @return {@code true} = valid, {@code false} = invalid.
    */
   public boolean isValid() {
      return getErrorMessage() == null;
   }
   
   /**
    * Returns an error message if the given parameters are invalid.
    * @return The error message or {@code null} if the parameters are valid.
    */
   public String getErrorMessage() {
      if (isShowHelp()) {
         return null; // valid
      }
      else {
         if (!isNumberOfRoundsValid()) {
            return "Value \"" + getNumberOfRoundsText() + " \" is no valid positive integer.";
         }
         if (StringUtil.isTrimmedEmpty(getOutputPath())) {
            return "No output path defined.";
         }
         else if (!new File(getOutputPath()).isDirectory()) {
            return "Output path \"" + getOutputPath() + "\" is no existing directory.";
         }
         else if (getBootClassPath() != null && !new File(getBootClassPath()).exists()) {
            return "Boot class path \"" + getBootClassPath() + "\" does not exist.";
         }
         else if (getLocations().isEmpty()) {
            return "No locations defined.";
         }
         else {
            String message = null;
            Iterator<String> iter = getLocations().iterator();
            while (message == null && iter.hasNext()) {
               String location = iter.next();
               if (!new File(location).exists()) {
                  message = "Location \"" + location + "\" does not exist.";
               }
            }
            return message;
         }
      }
   }
   
   /**
    * Parses the given parameters from the main method into a
    * {@link MonKeYBatchModeParameters} instance.
    * @param parameters The main parameters to parse.
    * @return The created {@link MonKeYBatchModeParameters} instance.
    */
   public static MonKeYBatchModeParameters analyze(String[] parameters) {
      MonKeYBatchModeParameters result = new MonKeYBatchModeParameters();
      if (parameters.length >= 1) {
         String previousParam = null;
         for (String param : parameters) {
            if (previousParam == null) {
               if (PARAM_SHOW_HELP.equals(param)) {
                  result.showHelp = true;
                  previousParam = null;
               }
               else if (PARAM_MAIN_WINDOW_OFF.equals(param)) {
                  result.mainWindowOff = true;
                  previousParam = null;
               }
               else if (PARAM_METHOD_TREATMENT_CONTRACT.equals(param)) {
                  result.methodTreatmentContract = true;
                  previousParam = null;
               }
               else if (PARAM_DEPENDENCY_CONTRACTS_OFF.equals(param)) {
                  result.dependencyContractsOff = true;
                  previousParam = null;
               }
               else if (PARAM_QUERY_TREATMENT_OFF.equals(param)) {
                  result.queryTreatmentOff = true;
                  previousParam = null;
               }
               else if (PARAM_ARITHMETIC_TREATMENT_BASE.equals(param)) {
                  result.arithmeticTreatmentBase = true;
                  previousParam = null;
               }
               else if (PARAM_STOP_AT_UNCLOSABLE.equals(param)) {
                  result.stopAtUnclosable = true;
                  previousParam = null;
               }
               else if (PARAM_DUMMY_LOAD_OFF.equals(param)) {
                  result.dummyLoadOff = true;
                  previousParam = null;
               }
               else if (PARAM_MAX_RULES.equals(param)) {
                  previousParam = param;
               }
               else if (PARAM_BOOT_CLASS_PATH.equals(param)) {
                  previousParam = param;
               }
               else if (PARAM_OUTPUT_PATH.equals(param)) {
                  previousParam = param;
               }
               else if (PARAM_ROUNDS.equals(param)) {
                  previousParam = param;
               }
               else if (param.startsWith(PARAM_LOAD_PREFIX)) {
                  previousParam = param;
               }
               else {
                  result.getLocations().add(param);
               }
            }
            else {
               if (PARAM_MAX_RULES.equals(previousParam)) {
                  try {
                     result.maxRuleApplications = Integer.parseInt(param);
                  }
                  catch (NumberFormatException e) {
                     throw new IllegalArgumentException("Max. Rule Applications (" + param + ") is not an integer number.");
                  }
                  if (result.maxRuleApplications < 0) {
                     throw new IllegalArgumentException("Max. Rule Applications (" + result.maxRuleApplications + ") can not be negative.");
                  }
                  previousParam = null;
               }
               else if (PARAM_BOOT_CLASS_PATH.equals(previousParam)) {
                  result.bootClassPath = param;
                  previousParam = null;
               }
               else if (PARAM_OUTPUT_PATH.equals(previousParam)) {
                  result.outputPath = param;
                  previousParam = null;
               }
               else if (PARAM_ROUNDS.equals(previousParam)) {
                  result.numberOfRoundsText = param;
                  previousParam = null;
               }
               else if (previousParam.startsWith(PARAM_LOAD_PREFIX)) {
                  result.locationLoadDirectories.put(Integer.valueOf(previousParam.substring(PARAM_LOAD_PREFIX.length())), param);
                  previousParam = null;
               }
               else {
                  Assert.isTrue(false, "Unsupported previous parameter \"" + previousParam + "\".");
               }
            }
         }
      }
      else {
         result.showHelp = true;
      }
      return result;
   }
   
   /**
    * Returns the location which provides proof files to load for the given location index.
    * @param locationIndex The location index.
    * @return The location load directory if available.
    */
   public String getLocationLoadDirectory(int locationIndex) {
      return locationLoadDirectories.get(Integer.valueOf(locationIndex));
   }
}