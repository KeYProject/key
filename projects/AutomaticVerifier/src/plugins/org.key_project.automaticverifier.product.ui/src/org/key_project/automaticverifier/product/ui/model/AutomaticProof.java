package org.key_project.automaticverifier.product.ui.model;

import org.eclipse.core.runtime.Assert;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.SwingUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
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
     * Bean property {@link #getNodes()}.
     */
    private static final String PROP_NODES = "nodes";

    /**
     * Bean property {@link #getBranches()}.
     */
    private static final String PROP_BRANCHES = "branches";

    /**
     * Bean property {@link #getTime()}.
     */
    private static final String PROP_TIME = "time";

    /**
     * The {@link InitConfig} that contains the {@link OperationContract} to proof.
     */
    private InitConfig initConfig;

    /**
     * The {@link Contract} to proof.
     */
    private Contract contract;
        
    /**
     * The type.
     */
    private String typeName;
    
    /**
     * The target.
     */
    private String targetName;
    
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
     * The number of proof nodes.
     */
    private int nodes;
    
    /**
     * The number of proof branches.
     */
    private int branches;
    
    /**
     * The elapsed time in the proof.
     */
    private long time;
    
    /**
     * The time when the proof was started.
     */
    private long proofStartTime;
    
    /**
     * Constructor.
     * @param typeName The type.
     * @param targetName The target. 
     * @param contractName The contract.
     * @param initConfig The {@link InitConfig} that contains the {@link OperationContract} to proof.
     * @param contract The {@link Contract} to proof.
     */
    public AutomaticProof(String typeName, 
                          String targetName, 
                          String contractName,
                          InitConfig initConfig,
                          Contract contract) {
        super();
        Assert.isNotNull(initConfig);
        Assert.isNotNull(contract);
        this.typeName = typeName;
        this.targetName = targetName;
        this.contractName = contractName;
        this.initConfig = initConfig;
        this.contract = contract;
    }

    /**
     * Returns the type.
     * @return The type.
     */
    public String getTypeName() {
        return typeName;
    }

    /**
     * Returns the target.
     * @return The target.
     */
    public String getTargetName() {
        return targetName;
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
       // Make sure that the proof was not executed before.
       if (proof == null) {
           IRunnableWithResult<Proof> run = new AbstractRunnableWithResult<Proof>() {
               @Override
               public void run() {
                   try {
                       ProofOblInput input = contract.createProofObl(initConfig, contract);
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
           // Start interactive proof automatically
           proofStartTime = System.currentTimeMillis();
           KeYUtil.runProofInAutomaticModeWithoutResultDialog(proof);
           // Update statistics
           updateStatistics();
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
     * Updates the statistics
     * {@link #getNodes()}, {@link #getBranches()} and {@link #getTime()}.
     */
    protected void updateStatistics() {
        setTime(System.currentTimeMillis() - proofStartTime);
        setNodes(proof.countNodes());
        setBranches(proof.countBranches());
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
    
    /**
     * Returns the number of proof nodes.
     * @return The number of proof nodes.
     */
    public int getNodes() {
        return nodes;
    }

    /**
     * Sets the number of proof nodes.
     * @param nodes The number of proof nodes to set.
     */
    public void setNodes(int nodes) {
        int oldValue = getNodes();
        this.nodes = nodes;
        firePropertyChange(PROP_NODES, oldValue, getNodes());
    }

    /**
     * Returns the number of branches.
     * @return The number of branches.
     */
    public int getBranches() {
        return branches;
    }

    /**
     * Sets the number of branches.
     * @param branches The number of branches to set.
     */
    public void setBranches(int branches) {
        int oldValue = getBranches();
        this.branches = branches;
        firePropertyChange(PROP_BRANCHES, oldValue, getBranches());
    }

    /**
     * Returns the elapsed time.
     * @return The elapsed time.
     */
    public long getTime() {
        return time;
    }

    /**
     * Sets the elapsed time.
     * @param time The elapsed time to set.
     */
    public void setTime(long time) {
        long oldValue = getTime();
        this.time = time;
        firePropertyChange(PROP_TIME, oldValue, getTime());
    }

    /**
     * Checks if a proof result is available.
     * @return {@code true} proof result is available, {@code false} no proof result available.
     */
    public boolean hasResult() {
        return getResult() != null && !AutomaticProofResult.UNKNOWN.equals(getResult());
    }
}
