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
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.po.SymbolicExecutionFunctionalOperationContractPO;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

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
          Proof proof = instantiateProof(configuration, method, useExistingContract, existingContract);
          if (proof == null) {
              throw new CoreException(LogUtil.getLogger().createErrorStatus("Proof was not instantiated."));
          }
          // Add debug target to ILaunch
          boolean showMethodReturnValues = KeySEDUtil.isShowMethodReturnValuesInDebugNodes(configuration);
          KeYLaunchSettings settings = new KeYLaunchSettings(method, useExistingContract, existingContract, showMethodReturnValues); // An unmodifiable backup of the ILaunchConfiguration because the ILaunchConfiguration may change during launch execution
          KeYDebugTarget target = new KeYDebugTarget(launch, MainWindow.getInstance().getMediator(), proof, settings);
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
     * @return The instantiated {@link Proof} instance in KeY.
     * @throws Exception Occurred Exception
     */
    protected Proof instantiateProof(final ILaunchConfiguration configuration,
                                     final IMethod method,
                                     final boolean useExistingContract,
                                     final String existingContract) throws Exception {
        // make sure that the method has a resource
        Assert.isNotNull(method.getResource(), "Method \"" + method + "\" is not part of a workspace resource.");
        // Make sure that the location is contained in a Java project
        IProject project = method.getResource().getProject();
        Assert.isTrue(JDTUtil.isJavaProject(project), " The project \"" + project + "\" is no Java project.");
        // Get source paths from class path
        List<File> sourcePaths = JDTUtil.getSourceLocations(project);
        Assert.isTrue(1 == sourcePaths.size(), "Multiple source paths are not supported.");
        // Get KeY project settings
        final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
        final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
        // Get local file for the eclipse resource
        final File location = sourcePaths.get(0);
        Assert.isNotNull(location, "The resource \"" + method.getResource() + "\" is not local.");
        // Open main window to avoid repaint bugs
        KeYUtil.openMainWindow();
        // Load location and open proof management dialog
        IRunnableWithResult<Proof> run = new AbstractRunnableWithResult<Proof>() {
            @Override
            public void run() {
                try {
                    // Make sure that main window is available.
                    Assert.isTrue(MainWindow.hasInstance(), "KeY main window is not available.");
                    MainWindow main = MainWindow.getInstance();
                    Assert.isNotNull(main, "KeY main window is not available.");
                    // Load location
                    InitConfig initConfig = KeYUtil.internalLoad(location, classPaths, bootClassPath, true);
                    // Get method to proof in KeY
                    ProgramMethod pm = KeYUtil.getProgramMethod(method, initConfig.getServices().getJavaInfo());
                    Assert.isNotNull(pm, "Can't find method \"" + method + "\" in KeY.");
                    // Get contract to proof
                    Contract contract = null;
                    KeYJavaType type = pm.getContainerType();
                    if (useExistingContract) {
                        ImmutableSet<FunctionalOperationContract> operationContracts = initConfig.getServices().getSpecificationRepository().getOperationContracts(type, pm);
                        contract = KeySEDUtil.findContract(operationContracts, existingContract);
                        if (contract == null) {
                            throw new CoreException(LogUtil.getLogger().createErrorStatus("Can't find contract \"" + existingContract + "\" of method \"" + JDTUtil.getQualifiedMethodLabel(method) + "\". Please update the launch configuration \"" + configuration.getName() + "\"."));
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
//                        input = contract.createProofObl(initConfig, contract);                        
                    }
                    ProblemInitializer init = main.getUserInterface().createProblemInitializer();
                    Proof proof = init.startProver(initConfig, input);
                    setResult(proof);
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
}
