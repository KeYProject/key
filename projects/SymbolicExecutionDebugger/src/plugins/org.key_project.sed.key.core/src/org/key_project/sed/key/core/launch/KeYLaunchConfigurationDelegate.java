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
import org.key_project.sed.core.model.memory.SEDMemoryBranchCondition;
import org.key_project.sed.core.model.memory.SEDMemoryBranchNode;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryExceptionalTermination;
import org.key_project.sed.core.model.memory.SEDMemoryMethodCall;
import org.key_project.sed.core.model.memory.SEDMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.core.model.memory.SEDMemoryTermination;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.key.core.launch.key.po.SEDFunctionalOperationContractPO;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.core.util.LogUtil;
import org.key_project.util.java.SwingUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.notification.NotificationEventID;
import de.uka.ilkd.key.gui.notification.NotificationTask;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;

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
           SEDMemoryDebugTarget target = new SEDMemoryDebugTarget(launch);
           target.setName("Fixed Example Target");
           launch.addDebugTarget(target);
           
           SEDMemoryThread thread = new SEDMemoryThread(target);
           thread.setName("Fixed Example Thread");
           target.addSymbolicThread(thread);
           
           SEDMemoryStatement s1 = new SEDMemoryStatement(target, thread, thread);
           s1.setName("int x = 1;");
           thread.addChild(s1);
           
           SEDMemoryStatement s2 = new SEDMemoryStatement(target, s1, thread);
           s2.setName("int y = 2;");
           s1.addChild(s2);
           
           SEDMemoryStatement s3 = new SEDMemoryStatement(target, s2, thread);
           s3.setName("int result = (x + y) / z;");
           s2.addChild(s3);
           
           SEDMemoryBranchCondition bzero = new SEDMemoryBranchCondition(target, s3, thread);
           bzero.setName("z == 0");
           s3.addChild(bzero);
           
           SEDMemoryExceptionalTermination et = new SEDMemoryExceptionalTermination(target, bzero, thread);
           et.setName("throws DivisionByZeroException()");
           bzero.addChild(et);
           
           SEDMemoryBranchCondition bnotzero = new SEDMemoryBranchCondition(target, s3, thread);
           bnotzero.setName("z != 0");
           s3.addChild(bnotzero);

           SEDMemoryMethodCall call = new SEDMemoryMethodCall(target, bnotzero, thread);
           call.setName("foo(result)");
           bnotzero.addChild(call);       

           SEDMemoryBranchNode branch = new SEDMemoryBranchNode(target, call, thread);
           branch.setName("if (result >= 0)");
           call.addChild(branch);
           
           SEDMemoryBranchCondition bnegative = new SEDMemoryBranchCondition(target, branch, thread);
           bnegative.setName("result < 0");
           branch.addChild(bnegative);
           
           SEDMemoryMethodReturn returnNegative = new SEDMemoryMethodReturn(target, bnegative, thread);
           returnNegative.setName("return -1");
           bnegative.addChild(returnNegative);
           
           SEDMemoryTermination terminationNegative = new SEDMemoryTermination(target, returnNegative, thread);
           terminationNegative.setName("<end>");
           returnNegative.addChild(terminationNegative);
           
           SEDMemoryBranchCondition bpositive = new SEDMemoryBranchCondition(target, branch, thread);
           bpositive.setName("result >= 0");
           branch.addChild(bpositive);
           
           SEDMemoryMethodReturn returnPositive = new SEDMemoryMethodReturn(target, bpositive, thread);
           returnPositive.setName("return 1");
           bpositive.addChild(returnPositive);
           
           SEDMemoryTermination terminationPositive = new SEDMemoryTermination(target, returnPositive, thread);
           terminationPositive.setName("<end>");
           returnPositive.addChild(terminationPositive);
           
//            // Get method and debug settings
//            final IMethod method = KeySEDUtil.findMethod(launch);
//            if (method == null) {
//                throw new CoreException(LogUtil.getLogger().createErrorStatus("Defined method does not exist. Please update the launch configuration \"" + configuration.getName() + "\"."));
//            }
//            final boolean useExistingContract = KeySEDUtil.isUseExistingContractValue(configuration);
//            final String existingContract = KeySEDUtil.getExistingContractValue(configuration);
//            if (useExistingContract && StringUtil.isTrimmedEmpty(existingContract)) {
//                throw new CoreException(LogUtil.getLogger().createErrorStatus("No existing contract defined. Please update the launch configuration \"" + configuration.getName() + "\"."));
//            }
//            // Instantiate proof
//            Proof proof = instantiateProof(configuration, method, useExistingContract, existingContract);
//            if (proof == null) {
//                throw new CoreException(LogUtil.getLogger().createErrorStatus("Proof was not instantiated."));
//            }
//            // Run proof
//            runProof(proof);
//            // Analyze proof
//            analyzeProof(proof);
        }
//        catch (CoreException e) {
//            throw e;
//        }
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
                        // Create TextualJMLSpecCase
                        ImmutableList<String> mods = ImmutableSLList.nil();
                        mods = mods.append("public");
                        TextualJMLSpecCase textualSpecCase = new TextualJMLSpecCase(mods, Behavior.NORMAL_BEHAVIOR);
                        if (!pm.isStatic()) {
                           textualSpecCase.addRequires(new PositionedString("self.<inv>")); // Assume own invariants
                        }
                        // Create contract
                        JMLSpecFactory factory = new JMLSpecFactory(services);
                        ImmutableSet<Contract> contracts = factory.createJMLOperationContracts(pm, textualSpecCase);
                        contract = contracts.iterator().next();
                    }
                    // Make sure that a contract is defined
                    if (contract == null) {
                        throw new CoreException(LogUtil.getLogger().createErrorStatus("Unable to find a contract to prove."));
                    }
                    // Instantiate proof
                    ProofOblInput input;
                    if (contract instanceof FunctionalOperationContract) {
                        input = new SEDFunctionalOperationContractPO(initConfig, (FunctionalOperationContract)contract);
                    }
                    else {
                        throw new CoreException(LogUtil.getLogger().createErrorStatus("Contract of class \"" + contract.getClass().getCanonicalName() + "\" are not supported."));
//                        input = contract.createProofObl(initConfig, contract);                        
                    }
                    ProblemInitializer init = main.createProblemInitializer();
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
    
    /**
     * Tries to close the given {@link Proof} instance in KeY with
     * the automatic mode.
     * @param proof The {@link Proof} to execute.
     */
    protected void runProof(Proof proof) {
        // Make sure that main window is available.
        Assert.isTrue(MainWindow.hasInstance(), "KeY main window is not available.");
        MainWindow main = MainWindow.getInstance();
        Assert.isNotNull(main, "KeY main window is not available.");
        // Run proof
        NotificationTask task = null;
        try {
            // Deactivate proof closed dialog
            task = main.getNotificationManager().getNotificationTask(NotificationEventID.PROOF_CLOSED);
            if (task != null) {
                main.getNotificationManager().removeNotificationTask(task);
            }
            // Start interactive proof automatically
            main.getMediator().startAutoMode(proof.openEnabledGoals());
            // Wait for interactive prover
            KeYUtil.waitWhileMainWindowIsFrozen(main);
        }
        finally {
            if (task != null) {
                main.getNotificationManager().addNotificationTask(task);
            }
        }
    }

    /**
     * Analyzes the given Proof by printing the executed code in the console.
     * @param proof The Proof to analyze.
     */
    protected void analyzeProof(Proof proof) {
        analyzeNode(proof.root(), 0);
    }

    /**
     * <p>
     * Analyzes the given Proof by printing the executed code in the console.
     * </p>
     * <p>
     * <b>Attention :</b> A correct pruning requires at the moment that
     * the Taclet Option "runtimeExceptions" is set to "runtimeExceptions:allow".
     * Alternatively it is required to modify rule {@code assignment_to_reference_array_component}
     * in file {@code javaRules.key} by uncommenting {@code \add (!(#v=null) & lt(#se, length(#v)) & geq(#se,0) & arrayStoreValid(#v, #se0)==>)}. 
     * </p>
     * @param proof The Proof to analyze.
     */
    protected void analyzeNode(Node node, int level) {
        // Analyze node
        if (!node.isClosed()) { // Prune closed branches
            NodeInfo info = node.getNodeInfo();
            SourceElement statement = info.getActiveStatement();
            if (statement != null && statement.getPositionInfo() != null) {
                PositionInfo posInfo = statement.getPositionInfo();
                if (posInfo.getStartPosition() != Position.UNDEFINED) {
                    System.out.println(statement);
                }
            }
            // Iterate over children
            NodeIterator children = node.childrenIterator();
            while (children.hasNext()) {
               Node child = children.next();
               analyzeNode(child, level + 1);
            }
        }
    }
}
