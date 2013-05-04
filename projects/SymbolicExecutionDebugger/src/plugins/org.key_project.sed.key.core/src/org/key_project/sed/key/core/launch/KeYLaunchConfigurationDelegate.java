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
import java.io.IOException;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.IRunnableWithDocument;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.SwingUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.DefaultProblemLoader;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodSubsetPO;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * This {@link LaunchConfigurationDelegate} is responsible to start
 * the Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
public class KeYLaunchConfigurationDelegate extends LaunchConfigurationDelegate {
    /**
     * {@inheritDoc}
     */
    @Override
    public void launch(final ILaunchConfiguration configuration, 
                       String mode, 
                       ILaunch launch, 
                       IProgressMonitor monitor) throws CoreException {
       try {
          // Determine proof settings
          IMethod method = KeySEDUtil.findMethod(launch);
          boolean useExistingContract = KeySEDUtil.isUseExistingContractValue(configuration);
          String existingContract = KeySEDUtil.getExistingContractValue(configuration);
          String precondition = KeySEDUtil.getPrecondition(configuration);
          boolean newDebugSession = KeySEDUtil.isNewDebugSession(configuration);
          String proofFileToContinue = KeySEDUtil.getFileToLoadValue(configuration);
          boolean showKeYMainWindow = KeySEDUtil.isShowKeYMainWindow(configuration);
          boolean mergeBranchConditions = KeySEDUtil.isMergeBranchConditions(configuration);
          boolean showMethodReturnValues = KeySEDUtil.isShowMethodReturnValuesInDebugNodes(configuration);
          boolean showVariablesOfSelectedDebugNode = KeySEDUtil.isShowVariablesOfSelectedDebugNode(configuration);
          boolean executeMethodRange = KeySEDUtil.isExecuteMethodRange(configuration);
          Position methodRangeStart = new KeYUtil.CursorPosition(KeySEDUtil.getMethodRangeStartLine(configuration), KeySEDUtil.getMethodRangeStartColumn(configuration));
          Position methodRangeEnd = new KeYUtil.CursorPosition(KeySEDUtil.getMethodRangeEndLine(configuration), KeySEDUtil.getMethodRangeEndColumn(configuration));
          // Determine location and class path entries
          File location = null;
          List<File> classPaths = null;
          File bootClassPath = null;
          if (newDebugSession) {
             // make sure that the method has a resource
             Assert.isNotNull(method.getResource(), "Method \"" + method + "\" is not part of a workspace resource.");
             // Make sure that the location is contained in a Java project
             IProject project = method.getResource().getProject();
             Assert.isTrue(JDTUtil.isJavaProject(project), " The project \"" + project + "\" is no Java project.");
             // Get source paths from class path
             List<File> sourcePaths = JDTUtil.getSourceLocations(project);
             Assert.isTrue(1 == sourcePaths.size(), "Multiple source paths are not supported.");
             // Get KeY project settings
             bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
             classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
             // Get local file for the eclipse resource
             location = sourcePaths.get(0);
             Assert.isNotNull(location, "The resource \"" + method.getResource() + "\" is not local.");
          }
          else {
             // Make sure that proof file exists
             Assert.isNotNull(proofFileToContinue);
             IFile locationFile = ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(proofFileToContinue));
             Assert.isNotNull(locationFile);
             Assert.isTrue(locationFile.exists());
             location = ResourceUtil.getLocation(locationFile);
             Assert.isNotNull(location);
             Assert.isTrue(location.exists());
          }
          // Instantiate proof settings
          KeYLaunchSettings settings = new KeYLaunchSettings(newDebugSession, proofFileToContinue, method, useExistingContract, existingContract, precondition, showMethodReturnValues, showVariablesOfSelectedDebugNode, showKeYMainWindow, mergeBranchConditions, executeMethodRange, methodRangeStart, methodRangeEnd, location, classPaths, bootClassPath); // An unmodifiable backup of the ILaunchConfiguration because the ILaunchConfiguration may change during launch execution
          // Validate proof settings
          if (newDebugSession) {
             if (method == null) {
                throw new CoreException(LogUtil.getLogger().createErrorStatus("Defined method does not exist. Please update the launch configuration \"" + configuration.getName() + "\"."));
             }
             if (useExistingContract && StringUtil.isTrimmedEmpty(existingContract)) {
                throw new CoreException(LogUtil.getLogger().createErrorStatus("No existing contract defined. Please update the launch configuration \"" + configuration.getName() + "\"."));
             }
          }
          else {
             if (StringUtil.isTrimmedEmpty(proofFileToContinue)) {
                throw new CoreException(LogUtil.getLogger().createErrorStatus("No proof file to load defined. Please update the launch configuration \"" + configuration.getName() + "\"."));
             }
             else {
                try {
                   IFile locationFile = ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(proofFileToContinue));
                   if (locationFile == null || !locationFile.exists()) {
                      throw new IllegalArgumentException("Proof file \"" + proofFileToContinue + "\" don't exist.");
                   }
                }
                catch (Exception e) {
                   throw new CoreException(LogUtil.getLogger().createErrorStatus("Proof file to load don't exist.. Please update the launch configuration \"" + configuration.getName() + "\".", e));
                }
             }
          }
          // Instantiate proof
          SymbolicExecutionEnvironment<?> environment = instantiateProof(configuration, settings);
          if (environment == null) {
              throw new CoreException(LogUtil.getLogger().createErrorStatus("Symbolic execution environment was not instantiated."));
          }
          // Add debug target to ILaunch
          KeYDebugTarget target = new KeYDebugTarget(launch, environment, settings);
          launch.addDebugTarget(target);
       }
       catch (CoreException e) {
           throw e;
       }
       catch (Exception e) {
           throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
       }
    }

    /**
     * Instantiates a new proof in KeY.
     * @param configuration The {@link ILaunchConfiguration} that is executed.
     * @param settings The {@link KeYLaunchSettings} to use.
     * @return The instantiated {@link SymbolicExecutionEnvironment} which contains all relevant information for symbolic execution.
     * @throws Exception Occurred Exception
     */
    protected SymbolicExecutionEnvironment<?> instantiateProof(ILaunchConfiguration configuration,
                                                               KeYLaunchSettings settings) throws Exception {

       if (settings.isShowKeYMainWindow()) {
          return instantiateProofInUserInterface(configuration.getName(), settings);
       }
       else {
          return instantiateProofWithoutUserInterface(configuration.getName(), settings);
       }
    }
    
    protected SymbolicExecutionEnvironment<?> instantiateProofWithoutUserInterface(String launchConfigurationName,
                                                                                   KeYLaunchSettings settings) throws Exception {
       UserInterface ui = new CustomConsoleUserInterface(false);
       return instantiateProof(ui, launchConfigurationName, settings);
    }
    
    protected SymbolicExecutionEnvironment<?> instantiateProofInUserInterface(final String launchConfigurationName,
                                                                              final KeYLaunchSettings settings) throws Exception {
       // Open main window to avoid repaint bugs
       KeYUtil.openMainWindow();
       // Load location and open proof management dialog
       IRunnableWithResult<SymbolicExecutionEnvironment<?>> run = new AbstractRunnableWithResult<SymbolicExecutionEnvironment<?>>() {
           @Override
           public void run() {
               try {
                   // Make sure that main window is available.
                   Assert.isTrue(MainWindow.hasInstance(), "KeY main window is not available.");
                   MainWindow main = MainWindow.getInstance();
                   Assert.isNotNull(main, "KeY main window is not available.");
                   // Load proof in user interface
                   setResult(instantiateProof(main.getUserInterface(), launchConfigurationName, settings));
               }
               catch (Exception e) {
                   setException(e);
               }
           }
       };
       SwingUtil.invokeAndWait(run);
       if (run.getException() != null) {
           throw run.getException();
       }
       return run.getResult();
    }
    
    protected SymbolicExecutionEnvironment<?> instantiateProof(UserInterface ui, 
                                                               String launchConfigurationName, 
                                                               KeYLaunchSettings settings) throws Exception {
       // Load location
       DefaultProblemLoader loader = ui.load(settings.getLocation(), settings.getClassPaths(), settings.getBootClassPath()); 
       InitConfig initConfig = loader.getInitConfig();
       // Try to reuse already instantiated proof
       Proof proof = loader.getProof();
       if (proof == null) {
          // Create proof input
          ProofOblInput input = createProofInput(launchConfigurationName, initConfig, settings);
          // Create proof
          proof = ui.createProof(initConfig, input);
       }
       SymbolicExecutionUtil.configureProof(proof);
       // Create symbolic execution tree builder
       SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(ui.getMediator(), proof, settings.isMergeBranchConditions());
       builder.analyse();
       // Create environment used for symbolic execution
       return new SymbolicExecutionEnvironment<UserInterface>(ui, initConfig, builder);
    }
    
    /**
     * Creates a {@link ProofOblInput} for the given {@link IMethod}
     * with the settings defined via the given {@link KeYLaunchSettings}.
     * @param launchConfigurationName The name of the launch configuration.
     * @param initConfig The {@link InitConfig} which provides the source code.
     * @param settings The {@link KeYLaunchSettings} to use.
     * @return The created {@link ProofOblInput}.
     * @throws Exception Occurred Exception if it was not possible to instantiate a {@link ProofOblInput}.
     */
    protected ProofOblInput createProofInput(String launchConfigurationName,
                                             InitConfig initConfig, 
                                             KeYLaunchSettings settings) throws Exception {
       // Get method to proof in KeY
       IProgramMethod pm = KeYUtil.getProgramMethod(settings.getMethod(), initConfig.getServices().getJavaInfo());
       Assert.isNotNull(pm, "Can't find method \"" + settings.getMethod() + "\" in KeY.");
       // Instantiate proof
       AbstractOperationPO input;
       if (settings.isExecuteMethodRange()) {
          // Convert defined method range into positions used in KeY.
          Position start = settings.getMethodRangeStart();
          Position end = settings.getMethodRangeEnd();
          if (start != null || end != null) {
             PositionConverterRunnableWithDocument run = new PositionConverterRunnableWithDocument(settings);
             KeYUtil.runOnDocument(settings.getMethod(), run);
             start = run.getStart();
             end = run.getEnd();
          }
          // Instantiate proof obligation
          input = new ProgramMethodSubsetPO(initConfig,
                                            computeProofObligationName(pm, settings.getMethodRangeStart(), settings.getMethodRangeEnd()),
                                            pm, 
                                            settings.getPrecondition(), 
                                            start, 
                                            end,
                                            true,
                                            true);
       }
       else if (settings.isUseExistingContract()) {
          // Get contract to proof
          Contract contract = null;
          KeYJavaType type = pm.getContainerType();
          ImmutableSet<FunctionalOperationContract> operationContracts = initConfig.getServices().getSpecificationRepository().getOperationContracts(type, pm);
          contract = KeySEDUtil.findContract(operationContracts, settings.getExistingContract());
          // Make sure that a contract is defined
          if (contract == null) {
              throw new CoreException(LogUtil.getLogger().createErrorStatus("Can't find contract \"" + settings.getExistingContract() + "\" of method \"" + JDTUtil.getQualifiedMethodLabel(settings.getMethod()) + "\". Please update the launch configuration \"" + launchConfigurationName + "\"."));
          }
          // Instantiate proof obligation
          if (contract instanceof FunctionalOperationContract) {
             input = new FunctionalOperationContractPO(initConfig, (FunctionalOperationContract)contract, true, true);
          }
          else {
              throw new CoreException(LogUtil.getLogger().createErrorStatus("Contract of class \"" + contract.getClass().getCanonicalName() + "\" are not supported."));
          }
       }
       else {
          input = new ProgramMethodPO(initConfig, 
                                      computeProofObligationName(pm, null, null), 
                                      pm, 
                                      settings.getPrecondition(), 
                                      true,
                                      true);
       }
       return input;
    }
    
    /**
     * Computes the proof obligation name.
     * @param pm The {@link IProgramMethod} to execute.
     * @param startPosition An optional start position.
     * @param endPosition An optional end position.
     * @return The computed proof obligation name.
     * @throws IOException Occurred Exception.
     */
    protected String computeProofObligationName(IProgramMethod pm,
                                                Position startPosition,
                                                Position endPosition) throws IOException {
       StringBuffer sb = new StringBuffer();
       // Append method signature
       sb.append(ProgramMethodPO.getProgramMethodSignature(pm, false));
       // Append start position
       if (startPosition != null) {
          sb.append(" from ");
          sb.append(startPosition.toString());
       }
       // Append end position
       if (endPosition != null) {
          sb.append(" to ");
          sb.append(endPosition.toString());
       }
       return sb.toString();
    }
    
    /**
     * {@link IRunnableWithResult} implementation which converts 
     * {@link KeYLaunchSettings#getMethodRangeStart()} and
     * {@link KeYLaunchSettings#getMethodRangeEnd()} into {@link Position}s
     * used in KeY's recorder.
     * @author Martin Hentschel
     */
    protected static class PositionConverterRunnableWithDocument implements IRunnableWithDocument {
       /**
        * The {@link KeYLaunchSettings} which provides the {@link Position}s to convert.
        */
       private KeYLaunchSettings settings;
       
       /**
        * The converted start position.
        */
       private Position start;
       
       /**
        * The converted end position.
        */
       private Position end;

       /**
        * Constructor.
        * @param settings The {@link KeYLaunchSettings} which provides the {@link Position}s to convert.
        */
       public PositionConverterRunnableWithDocument(KeYLaunchSettings settings) {
          super();
          this.settings = settings;
       }

       /**
        * {@inheritDoc}
        */
       @Override
       public void run(IDocument document) throws CoreException {
          try {
             // Compute tab width in JDT
             int jdtTabWidth = JDTUtil.getTabWidth(settings.getMethod());
             // Convert position width JDT tab width into position with KeY's recorder tab width.
             start = conertCursorPositionToKeYPosition(document, jdtTabWidth, settings.getMethodRangeStart());
             end = conertCursorPositionToKeYPosition(document, jdtTabWidth, settings.getMethodRangeEnd());
          }
          catch (BadLocationException e) {
             throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
          }
       }

       /**
        * Converts the given JDT cursor position into a KeY's recorder position
        * which is different in the used tab size and in the starting index
        * which is {@code 0} instead of {@code 1} in JDT.
        * @param document The {@link IDocument} which contains the source code.
        * @param jdtTabWidth The tab width used in JDT.
        * @param cursorPosition JDT's cursor position to convert.
        * @return The equivalent position in KeY:
        * @throws BadLocationException Occurred Exception
        */
       protected Position conertCursorPositionToKeYPosition(IDocument document, int jdtTabWidth, Position cursorPosition) throws BadLocationException {
          if (cursorPosition != null) {
             // Change tab width which is in JDT 4 by default and always 8 in KeY
             Position cursorPositionWithKeYsTabWidth = KeYUtil.changeCursorPositionTabWidth(document, cursorPosition, jdtTabWidth, KeYUtil.RECORDER_TAB_SIZE);
             // Normalize column which starts at 1 in JDT and at 0 in KeY
             Position keyPosition = new Position(cursorPositionWithKeYsTabWidth.getLine(), cursorPositionWithKeYsTabWidth.getColumn() - 1);
             return keyPosition;
          }
          else {
             return null;
          }
       }

       /**
        * Returns the converted start position.
        * @return The converted start position.
        */
       public Position getStart() {
          return start;
       }

       /**
        * Returns the converted end position.
        * @return The converted end position.
        */
       public Position getEnd() {
          return end;
       }
    }
}
