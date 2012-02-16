package org.key_project.automaticverifier.product.ui.model;

import org.eclipse.core.runtime.Assert;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.util.bean.Bean;
import org.key_project.key4eclipse.util.java.SwingUtil;
import org.key_project.key4eclipse.util.java.thread.AbstractRunnableWithResult;
import org.key_project.key4eclipse.util.java.thread.IRunnableWithResult;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.notification.NotificationEventID;
import de.uka.ilkd.key.gui.notification.NotificationTask;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.OperationContract;

/**
 * Represents an automatic proof.
 * @author Martin Hentschel
 */
public class AutomaticProof extends Bean {
    /**
     * Bean property {@link #getResult()}.
     */
    public static final String PROP_RESULT = "result";
    
    /**
     * The {@link InitConfig} that contains the {@link OperationContract} to proof.
     */
    private InitConfig initConfig;

    /**
     * The {@link OperationContract} to proof.
     */
    private OperationContract oc;
        
    /**
     * The type.
     */
    private String typeName;
    
    /**
     * The operation.
     */
    private String operationName;
    
    /**
     * The contract.
     */
    private String contractName;
    
    /**
     * The result.
     */
    private AutomaticProofResult result = AutomaticProofResult.UNKNOWN;

    /**
     * The {@link Proof} instance in KeY.
     */
    private Proof proof;
    
    /**
     * Constructor.
     * @param typeName The type.
     * @param operationName The operation. 
     * @param contractName The contract.
     * @param initConfig The {@link InitConfig} that contains the {@link OperationContract} to proof.
     * @param oc The {@link OperationContract} to proof.
     */
    public AutomaticProof(String typeName, 
                          String operationName, 
                          String contractName,
                          InitConfig initConfig,
                          OperationContract oc) {
        super();
        Assert.isNotNull(initConfig);
        Assert.isNotNull(oc);
        this.typeName = typeName;
        this.operationName = operationName;
        this.contractName = contractName;
        this.initConfig = initConfig;
        this.oc = oc;
    }

    /**
     * Returns the type.
     * @return The type.
     */
    public String getTypeName() {
        return typeName;
    }

    /**
     * Returns the operation.
     * @return The operation.
     */
    public String getOperationName() {
        return operationName;
    }

    /**
     * Returns the contract.
     * @return The contract.
     */
    public String getContractName() {
        return contractName;
    }

    /**
     * Returns the result.
     * @return The result.
     */
    public AutomaticProofResult getResult() {
        return result;
    }
    
    /**
     * Starts the proof in KeY and tries to fulfill it automatically.
     * @throws Exception Occurred Exception.
     */
    public void startProof() throws Exception {
        // Check if it is required to start a task
        if (proof == null) {
            NotificationTask task = null;
            MainWindow main = null;
            try {
                // Create proof if required
                if (proof == null) {
                    IRunnableWithResult<Proof> run = new AbstractRunnableWithResult<Proof>() {
                        @Override
                        public void run() {
                            try {
                                ProofOblInput input = oc.createProofObl(initConfig, oc);
                                Assert.isNotNull(input);
                                Assert.isTrue(MainWindow.hasInstance());
                                MainWindow main = MainWindow.getInstance();
                                Assert.isNotNull(main);
                                ProblemInitializer init = main.createProblemInitializer();
                                Assert.isNotNull(init);
                                Proof proof = init.startProver(initConfig, input);
                                Assert.isNotNull(proof);
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
                    proof = run.getResult();
                    proof.addProofTreeListener(new ProofTreeAdapter() {
                        @Override
                        public void proofClosed(ProofTreeEvent e) {
                            handleProofClosed(e);
                        }
                    });
                    setResult(AutomaticProofResult.OPEN);
                }
                // Get main window
                Assert.isTrue(MainWindow.hasInstance());
                main = MainWindow.getInstance();
                Assert.isNotNull(main);
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
                if (main != null && task != null) {
                    main.getNotificationManager().addNotificationTask(task);
                }            
            }
        }
    }

    /**
     * When the proof instance in KeY was closed.
     * @param e The event.
     */
    protected void handleProofClosed(ProofTreeEvent e) {
        setResult(AutomaticProofResult.CLOSED);
    }

    /**
     * Sets the proof result.
     * @param result The result to set.
     */
    protected void setResult(AutomaticProofResult result) {
        AutomaticProofResult oldValue = getResult();
        this.result = result;
        firePropertyChange(PROP_RESULT, oldValue, getResult());
    }
}
