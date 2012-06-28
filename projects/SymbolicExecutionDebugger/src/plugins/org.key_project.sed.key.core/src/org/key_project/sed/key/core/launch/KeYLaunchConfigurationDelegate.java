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
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
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
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.po.SymbolicExecutionFunctionalOperationContractPO;
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
          // Instantiate proof
          boolean showKeYMainWindow = KeySEDUtil.isShowKeYMainWindow(configuration);
          SymbolicExecutionEnvironment<?> environment = instantiateProof(configuration, method, useExistingContract, existingContract, showKeYMainWindow);
          if (environment == null) {
              throw new CoreException(LogUtil.getLogger().createErrorStatus("Symbolic execution environment was not instantiated."));
          }
          // Add debug target to ILaunch
          boolean showMethodReturnValues = KeySEDUtil.isShowMethodReturnValuesInDebugNodes(configuration);
          boolean showVariablesOfSelectedDebugNode = KeySEDUtil.isShowVariablesOfSelectedDebugNode(configuration);
          KeYLaunchSettings settings = new KeYLaunchSettings(method, useExistingContract, existingContract, showMethodReturnValues, showVariablesOfSelectedDebugNode, showKeYMainWindow); // An unmodifiable backup of the ILaunchConfiguration because the ILaunchConfiguration may change during launch execution
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
     * @param method The {@link IMethod} to debug.
     * @param useExistingContract Use existing contracts?
     * @param existingContract The existing contract to use.
     * @return The instantiated {@link SymbolicExecutionEnvironment} which contains all relevant information for symbolic execution.
     * @throws Exception Occurred Exception
     */
    protected SymbolicExecutionEnvironment<?> instantiateProof(ILaunchConfiguration configuration,
                                     IMethod method,
                                     boolean useExistingContract,
                                     String existingContract,
                                     boolean showKeYMainWindow) throws Exception {
        // make sure that the method has a resource
        Assert.isNotNull(method.getResource(), "Method \"" + method + "\" is not part of a workspace resource.");
        // Make sure that the location is contained in a Java project
        IProject project = method.getResource().getProject();
        Assert.isTrue(JDTUtil.isJavaProject(project), " The project \"" + project + "\" is no Java project.");
        // Get source paths from class path
        List<File> sourcePaths = JDTUtil.getSourceLocations(project);
        Assert.isTrue(1 == sourcePaths.size(), "Multiple source paths are not supported.");
        // Get KeY project settings
        File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
        List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
        // Get local file for the eclipse resource
        File location = sourcePaths.get(0);
        Assert.isNotNull(location, "The resource \"" + method.getResource() + "\" is not local.");
        // Instantiate proof in KeY's main window.
        if (showKeYMainWindow) {
           return instantiateProofInUserInterface(configuration.getName(), method, useExistingContract, existingContract, location, bootClassPath, classPaths);
        }
        else {
           return instantiateProofWithoutUserInterface(configuration.getName(), method, useExistingContract, existingContract, location, bootClassPath, classPaths);
        }
    }
    
    protected SymbolicExecutionEnvironment<?> instantiateProofWithoutUserInterface(String launchConfigurationName,
                                                                                   IMethod method,
                                                                                   boolean useExistingContract,
                                                                                   String existingContract,
                                                                                   File location, 
                                                                                   File bootClassPath, 
                                                                                   List<File> classPaths) throws Exception {
       UserInterface ui = new CustomConsoleUserInterface(false);
       // Load location
       InitConfig initConfig = ui.load(location, classPaths, bootClassPath);
       // Create proof input
       ProofOblInput input = createProofInput(launchConfigurationName, initConfig, method, useExistingContract, existingContract);
       // Create proof
       Proof proof = ui.createProof(initConfig, input);
       // Create symbolic execution tree builder
       SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(ui.getMediator(), proof);
       // Create environment used for symbolic execution
       return new SymbolicExecutionEnvironment<UserInterface>(ui, initConfig, builder);
    }
    
    protected SymbolicExecutionEnvironment<?> instantiateProofInUserInterface(final String launchConfigurationName,
                                                                              final IMethod method,
                                                                              final boolean useExistingContract,
                                                                              final String existingContract,
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
                   ProofOblInput input = createProofInput(launchConfigurationName, initConfig, method, useExistingContract, existingContract);
                   // Create proof
                   Proof proof = MainWindow.getInstance().getUserInterface().createProof(initConfig, input);
                   // Create symbolic execution tree builder
                   SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(main.getMediator(), proof);
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
     * in the given {@link InitConfig} which uses a default operation contract
     * or the defined one.
     * @param launchConfigurationName The name of the launch configuration.
     * @param initConfig The {@link InitConfig} which provides the source code.
     * @param method The {@link IMethod} to start proof for.
     * @param useExistingContract Use an existing contract or generate default one?
     * @param existingContract The ID of the existing contract to use.
     * @return The created {@link ProofOblInput}.
     * @throws Exception Occurred Exception if it was not possible to instantiate a {@link ProofOblInput}.
     */
    protected ProofOblInput createProofInput(String launchConfigurationName,
                                             InitConfig initConfig, 
                                             IMethod method, 
                                             boolean useExistingContract, 
                                             String existingContract) throws Exception {
       // Get method to proof in KeY
       IProgramMethod pm = KeYUtil.getProgramMethod(method, initConfig.getServices().getJavaInfo());
       Assert.isNotNull(pm, "Can't find method \"" + method + "\" in KeY.");
       // Get contract to proof
       Contract contract = null;
       KeYJavaType type = pm.getContainerType();
       if (useExistingContract) {
           ImmutableSet<FunctionalOperationContract> operationContracts = initConfig.getServices().getSpecificationRepository().getOperationContracts(type, pm);
           contract = KeySEDUtil.findContract(operationContracts, existingContract);
           if (contract == null) {
               throw new CoreException(LogUtil.getLogger().createErrorStatus("Can't find contract \"" + existingContract + "\" of method \"" + JDTUtil.getQualifiedMethodLabel(method) + "\". Please update the launch configuration \"" + launchConfigurationName + "\"."));
           }
       }
       else {
           Services services = initConfig.getServices();
           contract = SymbolicExecutionUtil.createDefaultContract(services, pm);
       }
       // Make sure that a contract is defined
       if (contract == null) {
           throw new CoreException(LogUtil.getLogger().createErrorStatus("Unable to find a contract to prove."));
       }
       // Instantiate proof
       ProofOblInput input;
       if (contract instanceof FunctionalOperationContract) {
           input = new SymbolicExecutionFunctionalOperationContractPO(initConfig, (FunctionalOperationContract)contract);
       }
       else {
           throw new CoreException(LogUtil.getLogger().createErrorStatus("Contract of class \"" + contract.getClass().getCanonicalName() + "\" are not supported."));
//           input = contract.createProofObl(initConfig, contract);                        
       }
       return input;
    }
}
