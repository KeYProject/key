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
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;

import org.eclipse.core.runtime.Assert;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.monkey.product.ui.application.MonKeYApplication;
import org.key_project.monkey.product.ui.model.MonKeYProof;
import org.key_project.monkey.product.ui.model.MonKeYProofResult;
import org.key_project.monkey.product.ui.util.MonKeYUtil;
import org.key_project.monkey.product.ui.util.MonKeYUtil.MonKeYProofSums;
import org.key_project.util.eclipse.ApplicationUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Batch mode of MonKeY.
 * @author Martin Hentschel
 */
public class MonKeYBatchMode {
   /**
    * The ID of this application.
    */
   public static final String APPLICATION_ID = "org.key_project.monkey.product.ui.Batch";
   
   /**
    * Indicates that the first dummy load was done to avoid API parsing time
    * of KeY in statistics. 
    */
   private boolean dummyLoadDone = false;
   
   /**
    * Starts the batch mode with the given parameters.
    * @param parametersArray The parameters.
    * @throws Exception Occurred Exception.
    */
   public void start(String[] parametersArray) throws Exception {
      // Parse parameters
      MonKeYBatchModeParameters parameters = MonKeYBatchModeParameters.analyze(parametersArray);
      // Show help or error message if parameters are invalid
      if (parameters.isShowHelp()) {
         printHelp();
      }
      else {
         if (!parameters.isValid()) {
            System.out.println("Invalid parameters: " + parameters.getErrorMessage());
            System.out.println();
            printHelp();
         }
         else {
            // Create output sub directory
            SimpleDateFormat format = new SimpleDateFormat("yyyy-MM-dd kk-mm-ss SSS");
            File outputDir = new File(parameters.getOutputPath(), "MonKeY Batch Results " + format.format(new Date()));
            Assert.isTrue(!outputDir.exists(), "Output directory \"" + outputDir + "\" already exist.");
            outputDir.mkdirs();
            Assert.isTrue(outputDir.exists(), "Can't create output directory \"" + outputDir + "\".");
            System.out.println("Using output directory: " + outputDir);
            // Open main window if defined
            if (!parameters.isMainWindowOff()) {
               KeYUtil.openMainWindow();
            }
            // Execute batch verification
            doVerification(parameters, outputDir);
         }
      }
   }
   
   /**
    * Does the verification with the given parameters and saves the result
    * in the existing output directory.
    * @param parameters The parameters to use.
    * @param outputDir The output directory to use.
    * @throws Exception Occurred Exception.
    */
   protected void doVerification(MonKeYBatchModeParameters parameters, File outputDir) throws Exception {
      List<VerificationRoundResult> results = new LinkedList<VerificationRoundResult>();
      // Do verification number of rounds time.
      for (int i = 0; i < parameters.getNumberOfRounds(); i++) {
         List<VerificationRoundResult> result = doVerificationRound(parameters, outputDir, i + 1);
         results.addAll(result);
      }
      // Save results
      File roundsFile = new File(outputDir, "Rounds.csv");
      System.out.println("Saving rounds results to: " + roundsFile);
      saveCSV(results, roundsFile);
      // Save average results
      File averageResultFile = new File(outputDir, "Average.csv");
      System.out.println("Saving rounds average to: " + averageResultFile);
      saveAverage(results, averageResultFile);
   }

   /**
    * Does the verification one time for each defined location.
    * @param parameters The parameters to use.
    * @param outputDir The output directory to use.
    * @param round The number of the current round.
    * @return The {@link VerificationRoundResult}s.
    * @throws Exception Occurred Exception.
    */
   protected List<VerificationRoundResult> doVerificationRound(MonKeYBatchModeParameters parameters, File outputDir, int round) throws Exception {
      List<VerificationRoundResult> result = new LinkedList<VerificationRoundResult>();
      // Create round subdir
      File roundSubDir = new File(outputDir, "Round " + round);
      roundSubDir.mkdirs();
      // Start verification by extracting parameters
      System.out.println("Starting verification round " + round + " of " + parameters.getNumberOfRounds());
      boolean showMainWindow = !parameters.isMainWindowOff();
      File bootClassPath = !StringUtil.isTrimmedEmpty(parameters.getBootClassPath()) ? new File(parameters.getBootClassPath()) : null;
      int maxRuleApplications = parameters.getMaxRuleApplications();
      boolean expandMethods = !parameters.isMethodTreatmentContract();
      boolean useDependencyContracts = !parameters.isDependencyContractsOff();
      boolean useQuery = !parameters.isQueryTreatmentOff();
      boolean useDefOps = !parameters.isArithmeticTreatmentBase();
      boolean stopAtUnclosable = parameters.isStopAtUnclosable();
      int i = 1; // location index
      for (String location : parameters.getLocations()) {
         System.out.println("Loading location \"" + location + "\".");
         // Do dummy load to filter out API parsing time
         if (!dummyLoadDone) {
            if (!parameters.isDummyLoadOff()) {
               List<MonKeYProof> proofs = MonKeYUtil.loadSourceInKeY(null, 
                                                                     new File(location), 
                                                                     bootClassPath, 
                                                                     showMainWindow);
               removeProofEnvFromKeY(proofs);
            }
            dummyLoadDone = true;
         }
         // Load resource
         long loadStartTime = System.currentTimeMillis();
         List<MonKeYProof> proofs = MonKeYUtil.loadSourceInKeY(null, 
                                                               new File(location), 
                                                               bootClassPath, 
                                                               showMainWindow);
         long loadingTime = System.currentTimeMillis() - loadStartTime;
         System.out.println("Found " + proofs.size() + " proofs in location \"" + location + "\".");
         // Load proofs
         String loadDirectory = parameters.getLocationLoadDirectory(i);
         if (loadDirectory != null) {
            for (MonKeYProof proof : proofs) {
               System.out.println("Loading proof \"" + proof.getTypeName() + "#" + proof.getTargetName() + "\" from " + loadDirectory + File.separator + proof.getProofFileName());
               proof.loadProof(loadDirectory, bootClassPath != null ? bootClassPath.getAbsolutePath() : null);
            }
         }
         // Do the proofs
         for (MonKeYProof proof : proofs) {
            System.out.println("Starting proof \"" + proof.getTypeName() + "#" + proof.getTargetName() + "\"");
            proof.startProof(maxRuleApplications, expandMethods, useDependencyContracts, useQuery, useDefOps, stopAtUnclosable);
            System.out.println("Proof \"" + proof.getTypeName() + "#" + proof.getTargetName() + "\" finished with result " + proof.getResult() + " \" in " + proof.getTime() + " milliseconds");
         }
         // Save the proofs
         for (MonKeYProof proof : proofs) {
            System.out.println("Save proof \"" + proof.getTypeName() + "#" + proof.getTargetName() + "\"");
            proof.save(roundSubDir.getAbsolutePath());
         }
         // Save location/round result
         File proofResultFile = new File(roundSubDir, getLocationName(location) + ".csv");
         System.out.println("Saving proof results to: " + proofResultFile);
         saveCSV(proofs, location, round, proofResultFile);
         // Save location/round sum results
         File sumResultFile = new File(roundSubDir, getLocationName(location) + ".properties");
         System.out.println("Saving sum results to: " + sumResultFile);
         MonKeYProofSums sums = saveSums(proofs, loadingTime, location, round, sumResultFile);
         // Extend result
         result.add(new VerificationRoundResult(location, round, loadingTime, sums));
         // Remove proofs
         removeProofEnvFromKeY(proofs);
         // Update location index
         i++;
      }
      return result;
   }
   
   /**
    * Result of {@link MonKeYBatchMode#doVerificationRound(MonKeYBatchModeParameters, File, int)}.
    * @author Martin Hentschel
    */
   protected static class VerificationRoundResult {
      /**
       * The verified location.
       */
      private String location;
      
      /**
       * The current round.
       */
      private int round;
      
      /**
       * The loading time.
       */
      private long loadingTime;
      
      /**
       * The sums over all done {@link MonKeYProof}s.
       */
      private MonKeYProofSums sums;
      
      /**
       * Constructor.
       * @param location The verified location.
       * @param round The current round.
       * @param loadingTime The loading time.
       * @param sums The sums over all done {@link MonKeYProof}s.
       */
      public VerificationRoundResult(String location, int round, long loadingTime, MonKeYProofSums sums) {
         this.location = location;
         this.round = round;
         this.loadingTime = loadingTime;
         this.sums = sums;
      }
      
      /**
       * Returns the verified location.
       * @return The verified location.
       */
      public String getLocation() {
         return location;
      }
      
      /**
       * Returns the current round.
       * @return The current round.
       */
      public int getRound() {
         return round;
      }
      
      /**
       * Returns the loading time.
       * @return The loading time.
       */
      public long getLoadingTime() {
         return loadingTime;
      }
      
      /**
       * Returns the sums over all done {@link MonKeYProof}s.
       * @return The sums over all done {@link MonKeYProof}s.
       */
      public MonKeYProofSums getSums() {
         return sums;
      }
   }
   
   /**
    * Removes all given {@link MonKeYProof} from KeYs {@link MainWindow}.
    * @param proofs The {@link MonKeYProof} to remove.
    * @throws InvocationTargetException Occurred Exception.
    * @throws InterruptedException Occurred Exception.
    */
   protected void removeProofEnvFromKeY(List<MonKeYProof> proofs) throws InterruptedException, InvocationTargetException {
      for (MonKeYProof proof : proofs) {
         proof.removeProof();
      }
   }
   
   /**
    * Saves the sums over all done {@link MonKeYProof}s as CSV file.
    * @param proofs The done {@link MonKeYProof}s.
    * @param loadingTime The loading time.
    * @param location The verified location.
    * @param round The current round.
    * @param target The target to save to.
    * @return The computed sums.
    * @throws IOException Occurred Exception.
    */
   protected MonKeYProofSums saveSums(List<MonKeYProof> proofs, 
                                      long loadingTime, 
                                      String location, 
                                      int round, 
                                      File target) throws IOException {
      // Compute sums
      int numOfProofs = proofs.size();
      MonKeYProofSums sums = MonKeYUtil.computeSums(proofs);
      // Create properties content
      Properties props = new Properties();
      props.setProperty("location", location);
      props.setProperty("round", round + StringUtil.EMPTY_STRING);
      props.setProperty("loadingTime", loadingTime + StringUtil.EMPTY_STRING);
      props.setProperty("numberOfProofs", numOfProofs + StringUtil.EMPTY_STRING);
      props.setProperty("closedProofs", sums.getClosedCount() + StringUtil.EMPTY_STRING);
      props.setProperty("nodes", sums.getNodes() + StringUtil.EMPTY_STRING);
      props.setProperty("branches", sums.getBranches() + StringUtil.EMPTY_STRING);
      props.setProperty("time", sums.getTime() + StringUtil.EMPTY_STRING);
      props.setProperty("loadingAndTime", loadingTime + sums.getTime() + StringUtil.EMPTY_STRING);
      // Save file
      saveProperties(props, target);
      return sums;
   }
   
   /**
    * Saves the given {@link Properties} into the target {@link File}.
    * @param properties The {@link Properties} to save.
    * @param target The target {@link File} to save to.
    * @throws IOException Occurred Exception.
    */
   protected void saveProperties(Properties properties, File target) throws IOException {
      FileWriter writer = new FileWriter(target);
      try {
         properties.store(writer, null);
      }
      finally {
         writer.close();
      }
   }

   /**
    * Saves the done {@link MonKeYProof}s as CSV file.
    * @param proofs The done {@link MonKeYProof}s to save.
    * @param location The verified location.
    * @param round The current round.
    * @param target The target {@link File} to save to.
    * @throws IOException Occurred Exception
    */
   protected void saveCSV(List<MonKeYProof> proofs,
                          String location,
                          int round, 
                          File target) throws IOException {
      // Create CSV content
      StringBuffer sb = new StringBuffer();
      sb.append("Location");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Round");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Type");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Target");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Contract");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Proof Reuse");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Proof Result");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Nodes");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Branches");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Time (milliseconds)");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Goal with applicable rules");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Goal without applicable rules");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append(StringUtil.NEW_LINE);
      for (MonKeYProof proof : proofs) {
         sb.append(location);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(round);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proof.getTypeName());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proof.getTargetName());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proof.getContractName());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proof.getReuseStatus());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proof.getResult() != null ? proof.getResult().getDisplayText() : StringUtil.EMPTY_STRING);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proof.getNodes());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proof.getBranches());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proof.getTime());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proof.hasResult() & !MonKeYProofResult.CLOSED.equals(proof.getResult()) ? MonKeYUtil.toString(proof.isHasGoalWithApplicableRules()) : StringUtil.EMPTY_STRING);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proof.hasResult() & !MonKeYProofResult.CLOSED.equals(proof.getResult()) ? MonKeYUtil.toString(proof.isHasGoalWithoutApplicableRules()) : StringUtil.EMPTY_STRING);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(StringUtil.NEW_LINE);
      }
      // Save file
      saveStringBuffer(sb, target);
   }
   
   /**
    * Saves the given {@link StringBuffer} into the target {@link File}.
    * @param sb The {@link StringBuffer} to save.
    * @param target The target {@link File} to save to.
    * @throws IOException Occurred Exception
    */
   protected void saveStringBuffer(StringBuffer sb, File target) throws IOException {
      FileWriter writer = new FileWriter(target);
      try {
         writer.write(sb.toString());
      }
      finally {
         writer.close();
      }
   }
   
   /**
    * Extracts the location name from the given location path.
    * @param locationPath The location path.
    * @return The location name.
    */
   protected String getLocationName(String locationPath) {
      return IOUtil.getFileNameWithoutExtension(new File(locationPath).getName());
   }

   /**
    * Saves the accumulated results over all rounds as CSV file. 
    * @param results The round results.
    * @param target The target file to save to.
    * @throws IOException Occurred Exception.
    */
   protected void saveCSV(List<VerificationRoundResult> results, File target) throws IOException {
      // Create CSV content
      StringBuffer sb = new StringBuffer();
      sb.append("Location");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Round");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Load Time (milliseconds)");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Proofs");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Reused Proofs");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Closed Proofs");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Nodes");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Branches");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Time (milliseconds)");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Load & Time (milliseconds)");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append(StringUtil.NEW_LINE);
      for (VerificationRoundResult result : results) {
         sb.append(result.getLocation());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(result.getRound());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(result.getLoadingTime());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(result.getSums().getProofsCount());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(result.getSums().getReusedProofsCount());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(result.getSums().getClosedCount());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(result.getSums().getNodes());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(result.getSums().getBranches());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(result.getSums().getTime());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(result.getLoadingTime() + result.getSums().getTime());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(StringUtil.NEW_LINE);
      }
      // Save file
      saveStringBuffer(sb, target);
   }
   
   /**
    * Saves the average over all rounds as CSV file.
    * @param results The round results.
    * @param target The target file to save to.
    * @throws IOException Occurred Exception.
    */
   protected void saveAverage(List<VerificationRoundResult> results, File target) throws IOException {
      // Split results by location
      Map<String, List<VerificationRoundResult>> locationResults = new LinkedHashMap<String, List<VerificationRoundResult>>();
      for (VerificationRoundResult result : results) {
         List<VerificationRoundResult> list = locationResults.get(result.getLocation());
         if (list == null) {
            list = new LinkedList<VerificationRoundResult>();
            locationResults.put(result.getLocation(), list);
         }
         list.add(result);
      }
      // Create CSV content
      StringBuffer sb = new StringBuffer();
      sb.append("Location");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Rounds");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Average Load Time (milliseconds)");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Average Proofs");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Average Reused Proofs");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Average Closed Proofs");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Average Nodes");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Average Branches");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Average Time (milliseconds)");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append("Average Load & Time (milliseconds)");
      sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
      sb.append(StringUtil.NEW_LINE);
      for (Entry<String, List<VerificationRoundResult>> entry : locationResults.entrySet()) {
         // Compute average
         long loadingTimeSum = 0;
         int proofCountSum = 0;
         long proofReusedSum = 0;
         int closedProofsSum = 0;
         long nodesSum = 0;
         long branchesSum = 0;
         long timeSum = 0;
         long loadingAndTimeSum = 0;
         for (VerificationRoundResult result : entry.getValue()) {
            loadingTimeSum += result.getLoadingTime();
            proofCountSum += result.getSums().getProofsCount();
            proofReusedSum += result.getSums().getReusedProofsCount();
            closedProofsSum += result.getSums().getClosedCount();
            nodesSum += result.getSums().getNodes();
            branchesSum += result.getSums().getBranches();
            timeSum += result.getSums().getTime();
            loadingAndTimeSum += result.getLoadingTime() + result.getSums().getTime();
         }
         int rounds = entry.getValue().size();
         // Append CSV content
         sb.append(entry.getKey());
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(rounds);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(loadingTimeSum / rounds);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proofCountSum / rounds);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(proofReusedSum / rounds);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(closedProofsSum / rounds);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(nodesSum / rounds);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(branchesSum / rounds);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(timeSum / rounds);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(loadingAndTimeSum / rounds);
         sb.append(SWTUtil.CSV_VALUE_SEPARATOR);
         sb.append(StringUtil.NEW_LINE);
      }
      // Save file
      saveStringBuffer(sb, target);
   }

   /**
    * Prints the user help.
    */
   public void printHelp() {
      String definedLauncherName = ApplicationUtil.getLauncherName(); 
      String launcher = definedLauncherName != null ? definedLauncherName : "MonKeY";
      launcher += " " + MonKeYApplication.PARAM_BATCH_MODE + " " + ApplicationUtil.ECLIPSE_PARAMETER_NO_SPLASH;
      // Print title
      System.out.println("Batch verification with MonKeY.");
      System.out.println();
      // Print parameter signature
      System.out.print(launcher);
      System.out.println(" " + MonKeYBatchModeParameters.PARAM_SHOW_HELP);
      System.out.println(" or ");
      System.out.print(launcher);
      System.out.print(" [" + MonKeYBatchModeParameters.PARAM_ROUNDS + " <numberOfRounds>]");
      System.out.print(" [" + MonKeYBatchModeParameters.PARAM_MAIN_WINDOW_OFF + "]");
      System.out.print(" [" + MonKeYBatchModeParameters.PARAM_DUMMY_LOAD_OFF + "]");
      System.out.print(" [" + MonKeYBatchModeParameters.PARAM_METHOD_TREATMENT_CONTRACT + "]");
      System.out.print(" [" + MonKeYBatchModeParameters.PARAM_DEPENDENCY_CONTRACTS_OFF + "]");
      System.out.print(" [" + MonKeYBatchModeParameters.PARAM_QUERY_TREATMENT_OFF + "]");
      System.out.print(" [" + MonKeYBatchModeParameters.PARAM_ARITHMETIC_TREATMENT_BASE + "]");
      System.out.print(" [" + MonKeYBatchModeParameters.PARAM_STOP_AT_UNCLOSABLE + "]");
      System.out.print(" [" + MonKeYBatchModeParameters.PARAM_MAX_RULES + " <maxRules>]");
      System.out.print(" [" + MonKeYBatchModeParameters.PARAM_BOOT_CLASS_PATH + " <bootClassPath>]");
      System.out.print(" [" + MonKeYBatchModeParameters.PARAM_LOAD_PREFIX + "<indexInListOfLocations> <bootClassPath>]");
      System.out.print(" " + MonKeYBatchModeParameters.PARAM_OUTPUT_PATH + " " + "<outputPath>");
      System.out.println(" <listOfLocations>");
      System.out.println();
      // Print parameter explanation
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_SHOW_HELP + " Show this help.");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_ROUNDS + " The number of rounds each source location is verified. Default if not defined is 1.");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_MAIN_WINDOW_OFF + " If defined, KeY's main window is not opened during loading of a source location.");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_DUMMY_LOAD_OFF + " If defined, the first location is not loaded twice to avoid the initial parsing time of rules in statistics.");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_METHOD_TREATMENT_CONTRACT + " If defined, method treatment Contract is used istead of Expand.");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_DEPENDENCY_CONTRACTS_OFF + " If defined, dependency contracts Off is used instead of On.");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_QUERY_TREATMENT_OFF + " If defined, query treatment Off is used instead of On.");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_ARITHMETIC_TREATMENT_BASE + " If defined, arithmetic treatment Base is used instead of DefOps.");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_STOP_AT_UNCLOSABLE + " If defined, auto mode stops at first unclosable goal.");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_MAX_RULES + " An optional positiv integer number to limit the maximal applied rules per proof. The default value is " + MonKeYUtil.DEFAULT_MAX_RULE_APPLICATIONS + ".");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_BOOT_CLASS_PATH + " An optional boot class path which is used for all source locations.");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_OUTPUT_PATH + " The output directory in state proof results are written. In the defined directory is a sub directory with the current time created. It contains for each round one sub directory. For each source location is a CSV file with the proof results and a properties file with the accumulated results created. The main directory contains also CSV files with the accumulated results over all rounds and his averages.");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_LOAD_PREFIX + "<indexInListOfLocations> The directory which provides proof files to load for the location defined at index <indexInListOfLocations> starting with 1. Load directory for first location is defined via \"" + MonKeYBatchModeParameters.PARAM_LOAD_PREFIX + "1 D:\\Temp\\ProofFilesForLocation1\".");
      System.out.println("\t" + MonKeYBatchModeParameters.PARAM_SHOW_HELP + " ");
      System.out.println("\t" + "<listOfLocations>" + " The absoulte paths to the source directories. Each of them contains a complete project to verify with KeY.");
      // Example
      System.out.println();
      System.out.println("Example to verify two products three times: ");
      System.out.print(launcher);
      System.out.print(" " + MonKeYBatchModeParameters.PARAM_ROUNDS + " 3");
      System.out.print(" " + MonKeYBatchModeParameters.PARAM_BOOT_CLASS_PATH + " \"" + getExampleDir("BootClassFiles") + "\"");
      System.out.print(" " + MonKeYBatchModeParameters.PARAM_OUTPUT_PATH + " \"" + getExampleDir("MonKeY Batch Results") + "\"");
      System.out.print(" \"" + getExampleDir("Project 1 Source Code") + "\"");
      System.out.print(" \"" + getExampleDir("Project 2 Source Code") + "\"");
   }

   /**
    * Appends the directory name to the users home directory.
    * @param directoryName The directory name.
    * @return The example path to use.
    */
   protected String getExampleDir(String directoryName) {
      File home = IOUtil.getHomeDirectory();
      if (home != null) {
         return new File(home, directoryName).toString();
      }
      else {
         return directoryName;
      }
   }
}