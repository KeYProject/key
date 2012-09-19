package org.key_project.monkey.product.ui.model;

import java.io.File;
import java.io.IOException;

import org.eclipse.core.runtime.Assert;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.SwingUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.proof.DefaultProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * Represents a MonKeY proof which simplifies the automation of
 * {@link Proof} instantiation and automatic closing in KeY.
 * @author Martin Hentschel
 */
public class MonKeYProof extends Bean {
    /**
     * Bean property {@link #getResult()}.
     */
    public static final String PROP_RESULT = "result";

    /**
     * Bean property {@link #getNodes()}.
     */
    public static final String PROP_NODES = "nodes";

    /**
     * Bean property {@link #getBranches()}.
     */
    public static final String PROP_BRANCHES = "branches";

    /**
     * Bean property {@link #getTime()}.
     */
    public static final String PROP_TIME = "time";

    /**
     * Bean property {@link #getReuseStatus()}.
     */
    public static final String PROP_REUSE_STATUS = "reuseStatus";

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
    private MonKeYProofResult result = MonKeYProofResult.UNKNOWN;

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
     * The reuse status.
     */
    private String reuseStatus;

   /**
     * Constructor.
     * @param typeName The type.
     * @param targetName The target. 
     * @param contractName The contract.
     * @param initConfig The {@link InitConfig} that contains the {@link OperationContract} to proof.
     * @param contract The {@link Contract} to proof.
     */
    public MonKeYProof(String typeName, 
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
    public MonKeYProofResult getResult() {
        return result;
    }
    
    /**
     * Starts the proof in KeY and tries to fulfill it automatically.
     * @throws Exception Occurred Exception.
     */
    public void startProof(final boolean expandMethods,
                           final boolean useDependencyContracts,
                           final boolean useQuery,
                           final boolean useDefOps) throws Exception {
       // Check if the proof is still valid
       if (proof != null && !KeYUtil.isProofInUI(proof)) {
          // proof is invalid, reset this automatic proof instance
          proof = null; 
          setResult(MonKeYProofResult.UNKNOWN);
          updateStatistics();
       }
       // Instantiate new proof if required
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
                       ProblemInitializer init = main.getUserInterface().createProblemInitializer();
                       Assert.isNotNull(init);
                       Proof proof = init.startProver(initConfig, input, 0);
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
           setResult(MonKeYProofResult.OPEN);
           setReuseStatus("New Proof");
       }
       // Start auto mode if the proof has opened goals.
       if (proof != null && !proof.openEnabledGoals().isEmpty()) {
          SwingUtil.invokeAndWait(new Runnable() {
             @Override
             public void run() {
                // Set proof strategy options
                StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
                sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, expandMethods ? StrategyProperties.METHOD_EXPAND : StrategyProperties.METHOD_CONTRACT);
                sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, useDependencyContracts ? StrategyProperties.DEP_ON : StrategyProperties.DEP_OFF);
                sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, useQuery ? StrategyProperties.QUERY_ON : StrategyProperties.QUERY_OFF);
                sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, useDefOps ? StrategyProperties.NON_LIN_ARITH_DEF_OPS : StrategyProperties.NON_LIN_ARITH_NONE);
                proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
                // Make sure that the new options are used
                ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
                proof.setActiveStrategy(MainWindow.getInstance().getMediator().getProfile().getDefaultStrategyFactory().create(proof, sp));
             }
          });
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
        setResult(MonKeYProofResult.CLOSED);
    }
    
    /**
     * Updates the statistics
     * {@link #getNodes()}, {@link #getBranches()} and {@link #getTime()}.
     */
    protected void updateStatistics() {
        setTime(proof != null ? getTime() + (System.currentTimeMillis() - proofStartTime) : 0l);
        setNodes(proof != null ? proof.countNodes() : 0);
        setBranches(proof != null ? proof.countBranches() : 0);
    }

    /**
     * Sets the proof result.
     * @param result The result to set.
     */
    protected void setResult(MonKeYProofResult result) {
        MonKeYProofResult oldValue = getResult();
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
     * Returns the reuse status.
     * @return The reuse status.
     */
    public String getReuseStatus() {
        return reuseStatus;
    }

    /**
     * Sets the reuse status.
     * @param reuseStatus The reuse status to set.
     */
    public void setReuseStatus(String reuseStatus) {
        String oldValue = getReuseStatus();
        this.reuseStatus = reuseStatus;
        firePropertyChange(PROP_REUSE_STATUS, oldValue, getReuseStatus());
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
        return getResult() != null && !MonKeYProofResult.UNKNOWN.equals(getResult());
    }

    /**
     * Removes the complete proof environment of the current KeY proof
     * from the {@link MainWindow}.  
     */
    public void removeProofEnvFromKeY() {
       if (proof != null) {
          KeYUtil.removeFromProofList(MainWindow.getInstance(), proof);
       }
    }

   /**
    * Returns a unique file name in which this proof should be saved.
    * @return The unique file name to save proof in or {@code null} if no proof is already instantiated.
    */
   public String getProofFileName() {
      return getTypeName() + "_" + getTargetName() + "_" + getContractName() + "." + KeYUtil.PROOF_FILE_EXTENSION;
   }

   /**
    * Checks if a proof instance in KeY is available.
    * @return {@code true} KeY's proof instance is available, {@code false} is not available.
    */
   public boolean hasProofInKeY() {
      return proof != null;
   }

   /**
    * Checks if a proof file with the name provided via {@link #getProofFileName()}
    * exists.
    * @param proofDirectory The directory to save/load proof in/from.
    * @return {@code true} proof file exists, {@code false} proof file is not available.
    */
   public boolean existsProofFile(String proofDirectory) {
      String fileName = getProofFileName();
      if (fileName != null) {
         return new File(proofDirectory, fileName).exists();
      }
      else {
         return false;
      }
   }

   /**
    * Saves KeY's proof if available in the given directory with the 
    * file name provided via {@link #getProofFileName()}. Existing files
    * will be replaced.
    * @param proofDirectory The directory to save proof in.
    * @return {@code true} proof was saved, {@code false} no proof available to save.
    * @throws IOException Occurred Exception.
    */
   public boolean save(String proofDirectory) throws IOException {
      if (hasProofInKeY()) {
         File file = new File(proofDirectory, getProofFileName());
         ProofSaver saver = new ProofSaver(proof, file.getAbsolutePath(), Main.INTERNAL_VERSION);
         String errorMessage = saver.save();
         if (errorMessage != null) {
            throw new IOException(errorMessage);
         }
         else {
            return true;
         }
      }
      else {
         return false;
      }
   }

   /**
    * Loads the existing proof if available.
    * @param proofDirectory The directory to load proof from.
    * @param bootClassPath The boot class path to use.
    * @throws Exception Occurred Exception.
    */
   public void loadProof(final String proofDirectory,
                         final String bootClassPath) throws Exception {
      if (existsProofFile(proofDirectory)) {
         IRunnableWithResult<Proof> run = new AbstractRunnableWithResult<Proof>() {
            @Override
            public void run() {
                try {
                    KeYUtil.runWithoutResultDialog(new KeYUtil.IRunnableWithMainWindow() {
                       @Override
                       public void run(MainWindow main) throws Exception {
                          File bootClassPathFile = !StringUtil.isTrimmedEmpty(bootClassPath) ? new File(bootClassPath) : null;
                          DefaultProblemLoader loader = main.getUserInterface().load(new File(proofDirectory, getProofFileName()), null, bootClassPathFile);
                          setResult(loader.getProof());
                       }
                    });
                }
                catch (Exception e) {
                    setException(e);
                }
            }
        };
        proofStartTime = System.currentTimeMillis();
        SwingUtil.invokeAndWait(run);
        if (run.getException() != null) {
            setReuseStatus(run.getException().toString());
        }
        else {
           setReuseStatus("Loaded Proof");
           setResult(MonKeYProofResult.CLOSED);
           proof = run.getResult();
           updateStatistics();
        }
      }
   }

   /**
    * Checks if the proof was reused or not.
    * @return {@code true} proof was successfully reused, {@code false} proof reuse failed or was not tried.
    */
   public boolean isReused() {
      return "Loaded Proof".equals(getReuseStatus());
   }
}
