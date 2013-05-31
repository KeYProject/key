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

package org.key_project.sed.key.core.launch;

import java.io.File;
import java.util.List;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jdt.core.IMethod;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.key.core.model.KeYDebugTarget;

import de.uka.ilkd.key.java.Position;

/**
 * Contains the settings used in an {@link ILaunch} which contains a
 * {@link KeYDebugTarget} as unmodifiable backup of the initial
 * {@link ILaunchConfiguration}. This backup is required because changes on
 * the launch configuration are possible during launch execution.
 * @author Martin Hentschel
 */
public class KeYLaunchSettings {
   /**
    * {@code true} new debug session, {@code false} continue existing *.proof file.
    */
   private boolean newDebugSession;
   
   /**
    * The path to the proof file to continue.
    */
   private String proofFileToContinue;

   /**
    * The {@link IMethod} to debug.
    */
   private IMethod method;
   
   /**
    * Use an existing contract or generate default contract?
    */
   private boolean useExistingContract;
   
   /**
    * The ID of the existing contract to use.
    */
   private String existingContract;
   
   /**
    * The precondition.
    */
   private String precondition;
   
   /**
    * If this is {@code true} an {@link ISEDMethodReturn} will contain the return value,
    * but the performance will suffer.
    * If it is {@code false} only the name of the returned method is shown in an {@link ISEDMethodReturn}.
    */
   private boolean showMethodReturnValues;
   
   /**
    * Show variables of selected debug node?
    */
   private boolean showVariablesOfSelectedDebugNode;
   
   /**
    * Show KeY's main window?
    */
   private boolean showKeYMainWindow;
   
   /**
    * Merge branch conditions?
    */
   private boolean mergeBranchConditions;
   
   /**
    * {@code true} execute method range, {@code false} execute complete method body.
    */
   private boolean executeMethodRange;
   
   /**
    * The start of the method range to execute.
    */
   private Position methodRangeStart;
   
   /**
    * The end of the method range to execute.
    */
   private Position methodRangeEnd;

   /**
    * The launched location.
    */
   private File location;
   
   /**
    * The used class path entries.
    */
   private List<File> classPaths;
   
   /**
    * The used boot class path.
    */
   private File bootClassPath;
   
   /**
    * Constructor.
    * @param newDebugSession {@code true} new debug session, {@code false} continue existing *.proof file.
    * @param proofFileToContinue The path to the proof file to continue.
    * @param method The {@link IMethod} to debug.
    * @param useExistingContract Use an existing contract or generate default contract?
    * @param existingContract The ID of the existing contract to use.
    * @param precondition The precondition.
    * @param showMethodReturnValues Show method return values of {@link ISEDMethodReturn} instances?
    * @param showVariablesOfSelectedDebugNode Show variables of selected debug node?
    * @param showKeYMainWindow Show KeY's main window?
    * @param mergeBranchConditions Merge branch conditions?
    * @param executeMethodRange {@code true} execute method range, {@code false} execute complete method body.
    * @param methodRangeStart The start of the method range to execute.
    * @param methodRangeEnd The end of the method range to execute.
    * @param location The launched location.
    * @param classPaths The used class path entries.
    * @param bootClassPath The used boot class path.
    */
   public KeYLaunchSettings(boolean newDebugSession,
                            String proofFileToContinue,
                            IMethod method, 
                            boolean useExistingContract, 
                            String existingContract, 
                            String precondition,
                            boolean showMethodReturnValues,
                            boolean showVariablesOfSelectedDebugNode,
                            boolean showKeYMainWindow,
                            boolean mergeBranchConditions,
                            boolean executeMethodRange,
                            Position methodRangeStart,
                            Position methodRangeEnd,
                            File location,
                            List<File> classPaths,
                            File bootClassPath) {
      this.newDebugSession = newDebugSession;
      this.proofFileToContinue = proofFileToContinue;
      this.method = method;
      this.useExistingContract = useExistingContract;
      this.existingContract = existingContract;
      this.precondition = precondition;
      this.showMethodReturnValues = showMethodReturnValues;
      this.showVariablesOfSelectedDebugNode = showVariablesOfSelectedDebugNode;
      this.showKeYMainWindow = showKeYMainWindow;
      this.mergeBranchConditions = mergeBranchConditions;
      this.executeMethodRange = executeMethodRange;
      this.methodRangeStart = methodRangeStart;
      this.methodRangeEnd = methodRangeEnd;
      this.location = location;
      this.classPaths = classPaths;
      this.bootClassPath = bootClassPath;
   }
   
   /**
    * Checks if a new debug session should be started or an existing one continued.
    * @return {@code true} new debug session, {@code false} continue existing *.proof file.
    */
   public boolean isNewDebugSession() {
      return newDebugSession;
   }

   /**
    * Returns the path to the proof file to continue.
    * @return The path to the proof file to continue.
    */
   public String getProofFileToContinue() {
      return proofFileToContinue;
   }

   /**
    * Returns the {@link IMethod} to debug.
    * @return The {@link IMethod} to debug.
    */
   public IMethod getMethod() {
      return method;
   }

   /**
    * Checks if an existing contract or a generate default contract is used?
    * @return Use an existing contract or generate default contract?
    */
   public boolean isUseExistingContract() {
      return useExistingContract;
   }

   /**
    * Returns the ID of the existing contract to use.
    * @return The ID of the existing contract to use.
    */
   public String getExistingContract() {
      return existingContract;
   }

   /**
    * Checks if method return values of {@link ISEDMethodReturn} instances should be shown.
    * @return Show method return values of {@link ISEDMethodReturn} instances?
    */
   public boolean isShowMethodReturnValues() {
      return showMethodReturnValues;
   }

   /**
    * Checks if KeY's main window should be shown.
    * @return Show KeY's main window?
    */
   public boolean isShowKeYMainWindow() {
      return showKeYMainWindow;
   }

   /**
    * Checks if variables of selected debug node should be shown.
    * @return Show variables of selected debug node?
    */
   public boolean isShowVariablesOfSelectedDebugNode() {
      return showVariablesOfSelectedDebugNode;
   }

   /**
    * Checks if branch conditions are merged.
    * @return Merge branch conditions?
    */
   public boolean isMergeBranchConditions() {
      return mergeBranchConditions;
   }

   /**
    * Returns the precondition.
    * @return The precondition.
    */
   public String getPrecondition() {
      return precondition;
   }

   /**
    * Checks if a method range or the complete method is executed.
    * @return {@code true} execute method range, {@code false} execute complete method body.
    */
   public boolean isExecuteMethodRange() {
      return executeMethodRange;
   }

   /**
    * Returns the start of the method range to execute.
    * @return The start of the method range to execute.
    */
   public Position getMethodRangeStart() {
      return methodRangeStart;
   }

   /**
    * Returns the end of the method range to execute.
    * @return The end of the method range to execute.
    */
   public Position getMethodRangeEnd() {
      return methodRangeEnd;
   }

   /**
    * Returns the launched location.
    * @return The launched location.
    */
   public File getLocation() {
      return location;
   }

   /**
    * Returns the used class path entries.
    * @return The used class path entries.
    */
   public List<File> getClassPaths() {
      return classPaths;
   }

   /**
    * Returns the used boot class path.
    * @return The used boot class path.
    */
   public File getBootClassPath() {
      return bootClassPath;
   }
}