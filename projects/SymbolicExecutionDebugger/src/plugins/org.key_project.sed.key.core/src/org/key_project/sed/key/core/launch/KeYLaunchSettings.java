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
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.util.KeySEDUtil;

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
   private final boolean newDebugSession;
   
   /**
    * The path to the proof file to continue.
    */
   private final String proofFileToContinue;

   /**
    * The {@link IMethod} to debug.
    */
   private final IMethod method;
   
   /**
    * The signature of {@link #method} computed via {@link KeySEDUtil#getMethodValue(IMethod)}.
    */
   private final String methodSignature;
   
   /**
    * Use an existing contract or generate default contract?
    */
   private final boolean useExistingContract;
   
   /**
    * The ID of the existing contract to use.
    */
   private final String existingContract;
   
   /**
    * The precondition.
    */
   private final String precondition;
   
   /**
    * If this is {@code true} an {@link ISEDMethodReturn} will contain the return value,
    * but the performance will suffer.
    * If it is {@code false} only the name of the returned method is shown in an {@link ISEDMethodReturn}.
    */
   private final boolean showMethodReturnValues;
   
   /**
    * Show variables of selected debug node?
    */
   private final boolean showVariablesOfSelectedDebugNode;
   
   /**
    * Show KeY's main window?
    */
   private final boolean showKeYMainWindow;
   
   /**
    * Merge branch conditions?
    */
   private final boolean mergeBranchConditions;
   
   /**
    * {@code true} execute method range, {@code false} execute complete method body.
    */
   private final boolean executeMethodRange;
   
   /**
    * The start of the method range to execute.
    */
   private final Position methodRangeStart;
   
   /**
    * The end of the method range to execute.
    */
   private final Position methodRangeEnd;

   /**
    * The launched location.
    */
   private final File location;
   
   /**
    * The used class path entries.
    */
   private final List<File> classPaths;
   
   /**
    * The used boot class path.
    */
   private final File bootClassPath;
   
   /**
    * Use pretty printing?
    */
   private final boolean usePrettyPrinting;
   
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
    * @param usePrettyPrinting Use pretty printing?
    * @throws JavaModelException Occurred Exception.
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
                            File bootClassPath,
                            boolean usePrettyPrinting) throws JavaModelException {
      this.newDebugSession = newDebugSession;
      this.proofFileToContinue = proofFileToContinue;
      this.method = method;
      this.methodSignature = KeySEDUtil.getMethodValue(method); // It can't be done later because the method might be renamed and JDT throws than an exception. But now the method exists definitively.
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
      this.usePrettyPrinting = usePrettyPrinting;
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
    * Returns the signature of {@link #getMethod()} computed via {@link KeySEDUtil#getMethodValue(IMethod)}.
    * @return The signature of {@link #getMethod()} computed via {@link KeySEDUtil#getMethodValue(IMethod)}.
    */
   public String getMethodSignature() {
      return methodSignature;
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

   /**
    * Checks if pretty printing should be used.
    * @return {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   public boolean isUsePrettyPrinting() {
      return usePrettyPrinting;
   }
}