package org.key_project.sed.key.core.launch;

import java.io.File;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
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
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.SwingUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.po.MethodPartPO;
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
          // Get method and debug settings
          final IMethod method = KeySEDUtil.findMethod(launch);
          if (method == null) {
              throw new CoreException(LogUtil.getLogger().createErrorStatus("Defined method does not exist. Please update the launch configuration \"" + configuration.getName() + "\"."));
          }
          final boolean useExistingContract = KeySEDUtil.isUseExistingContractValue(configuration);
          final String existingContract = KeySEDUtil.getExistingContractValue(configuration);
          if (useExistingContract && StringUtil.isTrimmedEmpty(existingContract)) {
              throw new CoreException(LogUtil.getLogger().createErrorStatus("No existing contract defined. Please update the launch configuration \"" + configuration.getName() + "\"."));
          }
          final String precondition = KeySEDUtil.getPrecondition(configuration);
          // Instantiate proof
          boolean showKeYMainWindow = KeySEDUtil.isShowKeYMainWindow(configuration);
          boolean mergeBranchConditions = KeySEDUtil.isMergeBranchConditions(configuration);
          boolean showMethodReturnValues = KeySEDUtil.isShowMethodReturnValuesInDebugNodes(configuration);
          boolean showVariablesOfSelectedDebugNode = KeySEDUtil.isShowVariablesOfSelectedDebugNode(configuration);
          boolean executeMethodRange = KeySEDUtil.isExecuteMethodRange(configuration);
          Position methodRangeStart = new KeYUtil.CursorPosition(KeySEDUtil.getMethodRangeStartLine(configuration), KeySEDUtil.getMethodRangeStartColumn(configuration));
          Position methodRangeEnd = new KeYUtil.CursorPosition(KeySEDUtil.getMethodRangeEndLine(configuration), KeySEDUtil.getMethodRangeEndColumn(configuration));
          KeYLaunchSettings settings = new KeYLaunchSettings(method, useExistingContract, existingContract, precondition, showMethodReturnValues, showVariablesOfSelectedDebugNode, showKeYMainWindow, mergeBranchConditions, executeMethodRange, methodRangeStart, methodRangeEnd); // An unmodifiable backup of the ILaunchConfiguration because the ILaunchConfiguration may change during launch execution
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
        // make sure that the method has a resource
        Assert.isNotNull(settings.getMethod().getResource(), "Method \"" + settings.getMethod() + "\" is not part of a workspace resource.");
        // Make sure that the location is contained in a Java project
        IProject project = settings.getMethod().getResource().getProject();
        Assert.isTrue(JDTUtil.isJavaProject(project), " The project \"" + project + "\" is no Java project.");
        // Get source paths from class path
        List<File> sourcePaths = JDTUtil.getSourceLocations(project);
        Assert.isTrue(1 == sourcePaths.size(), "Multiple source paths are not supported.");
        // Get KeY project settings
        File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
        List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
        // Get local file for the eclipse resource
        File location = sourcePaths.get(0);
        Assert.isNotNull(location, "The resource \"" + settings.getMethod().getResource() + "\" is not local.");
        // Instantiate proof in KeY's main window.
        if (settings.isShowKeYMainWindow()) {
           return instantiateProofInUserInterface(configuration.getName(), settings, location, bootClassPath, classPaths);
        }
        else {
           return instantiateProofWithoutUserInterface(configuration.getName(), settings, location, bootClassPath, classPaths);
        }
    }
    
    protected SymbolicExecutionEnvironment<?> instantiateProofWithoutUserInterface(String launchConfigurationName,
                                                                                   KeYLaunchSettings settings,
                                                                                   File location, 
                                                                                   File bootClassPath, 
                                                                                   List<File> classPaths) throws Exception {
       UserInterface ui = new CustomConsoleUserInterface(false);
       // Load location
       InitConfig initConfig = ui.load(location, classPaths, bootClassPath);
       // Create proof input
       ProofOblInput input = createProofInput(launchConfigurationName, initConfig, settings);
       // Create proof
       Proof proof = ui.createProof(initConfig, input);
       // Create symbolic execution tree builder
       SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(ui.getMediator(), proof, settings.isMergeBranchConditions());
       // Create environment used for symbolic execution
       return new SymbolicExecutionEnvironment<UserInterface>(ui, initConfig, builder);
    }
    
    protected SymbolicExecutionEnvironment<?> instantiateProofInUserInterface(final String launchConfigurationName,
                                                                              final KeYLaunchSettings settings,
                                                                              final File location, 
                                                                              final File bootClassPath, 
                                                                              final List<File> classPaths) throws Exception {
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
                   // Load location
                   InitConfig initConfig = KeYUtil.internalLoad(location, classPaths, bootClassPath, true);
                   // Create proof input
                   ProofOblInput input = createProofInput(launchConfigurationName, initConfig, settings);
                   // Create proof
                   Proof proof = MainWindow.getInstance().getUserInterface().createProof(initConfig, input);
                   // Create symbolic execution tree builder
                   SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(main.getMediator(), proof, settings.isMergeBranchConditions());
                   // Create environment used for symbolic execution
                   setResult(new SymbolicExecutionEnvironment<UserInterface>(main.getUserInterface(), initConfig, builder));
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
          input = new MethodPartPO(initConfig, 
                                   pm.getFullName() + " from " + settings.getMethodRangeStart() + " to " + settings.getMethodRangeEnd(), 
                                   pm, 
                                   settings.getPrecondition(), 
                                   start, 
                                   end,
                                   true);
       }
       else {
          // Get contract to proof
          Contract contract = null;
          KeYJavaType type = pm.getContainerType();
          if (settings.isUseExistingContract()) {
              ImmutableSet<FunctionalOperationContract> operationContracts = initConfig.getServices().getSpecificationRepository().getOperationContracts(type, pm);
              contract = KeySEDUtil.findContract(operationContracts, settings.getExistingContract());
              if (contract == null) {
                  throw new CoreException(LogUtil.getLogger().createErrorStatus("Can't find contract \"" + settings.getExistingContract() + "\" of method \"" + JDTUtil.getQualifiedMethodLabel(settings.getMethod()) + "\". Please update the launch configuration \"" + launchConfigurationName + "\"."));
              }
          }
          else {
              Services services = initConfig.getServices();
              contract = SymbolicExecutionUtil.createDefaultContract(services, pm, settings.getPrecondition());
          }
          // Make sure that a contract is defined
          if (contract == null) {
              throw new CoreException(LogUtil.getLogger().createErrorStatus("Unable to find a contract to prove."));
          }
          // Instantiate proof obligation
          if (contract instanceof FunctionalOperationContract) {
             input = new FunctionalOperationContractPO(initConfig, (FunctionalOperationContract)contract, true);
          }
          else {
              throw new CoreException(LogUtil.getLogger().createErrorStatus("Contract of class \"" + contract.getClass().getCanonicalName() + "\" are not supported."));
          }
       }
       return input;
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
