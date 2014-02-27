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

package org.key_project.monkey.product.ui.model;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.util.Iterator;

import org.eclipse.core.runtime.Assert;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.ProofUserManager;
import org.key_project.monkey.product.ui.util.MonKeYUtil;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.SwingUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.DefaultProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.MiscTools;

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
     * Bean property {@link #isHasGoalWithApplicableRules()}.
     */
    public static final String PROP_HAS_GOAL_WITH_APPLICABLE_RULES = "hasGoalWithApplicableRules";

    /**
     * Bean property {@link #isHasGoalWithoutApplicableRules()}.
     */
    public static final String PROP_HAS_GOAL_WITHOUT_APPLICABLE_RULES = "hasGoalWithoutApplicableRules";
    
    /**
     * The {@link KeYEnvironment} to use.
     */
    private KeYEnvironment<?> environment;

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
     * If true at least one {@link Goal} has applicable rules left.
     */
    private boolean hasGoalWithApplicableRules;
    
    /**
     * If true at least one {@link Goal} has no applicable rules.
     */
    private boolean hasGoalWithoutApplicableRules;

   /**
     * Constructor.
     * @param typeName The type.
     * @param targetName The target. 
     * @param contractName The contract.
     * @param environment The {@link KeYEnvironment} to use.
     * @param contract The {@link Contract} to proof.
     */
    public MonKeYProof(String typeName, 
                       String targetName, 
                       String contractName,
                       KeYEnvironment<?> environment,
                       Contract contract) {
        Assert.isNotNull(environment);
        Assert.isNotNull(contract);
        this.typeName = typeName;
        this.targetName = targetName;
        this.contractName = contractName;
        this.environment = environment;
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
    public void startProof(final int maxRuleApplications,
                           final boolean expandMethods,
                           final boolean useDependencyContracts,
                           final boolean useQuery,
                           final boolean useDefOps,
                           final boolean stopAtUnclosable) throws Exception {
       // Start auto mode only if proof is not already closed.
       if (!MonKeYProofResult.CLOSED.equals(getResult())) {
          // Check if the proof is still valid
          if (proof != null && !proof.isDisposed()) {
             // proof is invalid, reset this automatic proof instance
             removeProof(); 
             setResult(MonKeYProofResult.UNKNOWN);
             updateStatistics();
          }
          // Instantiate new proof if required
          if (proof == null) {
              IRunnableWithResult<Proof> run = new AbstractRunnableWithResult<Proof>() {
                  @Override
                  public void run() {
                      try {
                          ProofOblInput input = contract.createProofObl(environment.getInitConfig(), contract);
                          Assert.isNotNull(input);
                          Proof proof = environment.getUi().createProof(environment.getInitConfig(), input);
                          Assert.isNotNull(proof);
                          ProofUserManager.getInstance().addUser(proof, environment, MonKeYProof.this);
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
                   sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, stopAtUnclosable ? StrategyProperties.STOPMODE_NONCLOSE : StrategyProperties.STOPMODE_DEFAULT);
                   proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
                   // Make sure that the new options are used
                   ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxRuleApplications);
                   ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
                   proof.getSettings().getStrategySettings().setMaxSteps(maxRuleApplications);
                   proof.setActiveStrategy(environment.getMediator().getProfile().getDefaultStrategyFactory().create(proof, sp));
                }
             });
             // Start interactive proof automatically
             proofStartTime = System.currentTimeMillis();
             if (MonKeYUtil.isMainWindowEnvironment(environment)) {
                KeYUtil.runProofInAutomaticModeWithoutResultDialog(proof); // Run auto mode without result dialog
             }
             else {
                environment.getUi().startAndWaitForAutoMode(proof); // Run auto mode outside of MainWindow where no result dialog exist
             }
             // Update statistics
             updateStatistics();
          }
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
        setTime((proof != null && !proof.isDisposed()) ? getTime() + (System.currentTimeMillis() - proofStartTime) : 0l);
        setNodes((proof != null && !proof.isDisposed()) ? proof.countNodes() : 0);
        setBranches((proof != null && !proof.isDisposed()) ? proof.countBranches() : 0);
        boolean hasGoalWithApplicableRules = false;
        boolean hasGoalWithoutApplicableRules = false;
        Iterator<Goal> iter = proof.openGoals().iterator();
        while ((!hasGoalWithApplicableRules || !hasGoalWithoutApplicableRules) && iter.hasNext()) {
           Goal next = iter.next();
           if (SymbolicExecutionUtil.hasApplicableRules(next)) {
              hasGoalWithApplicableRules = true;
           }
           else {
              hasGoalWithoutApplicableRules = true;
           }
        }
        setHasGoalWithApplicableRules(hasGoalWithApplicableRules);
        setHasGoalWithoutApplicableRules(hasGoalWithoutApplicableRules);
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
    protected void setNodes(int nodes) {
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
    protected void setReuseStatus(String reuseStatus) {
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
    protected void setBranches(int branches) {
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
    protected void setTime(long time) {
        long oldValue = getTime();
        this.time = time;
        firePropertyChange(PROP_TIME, oldValue, getTime());
    }

   /**
    * Checks if at least one goal with applicable rules is available.
    * @return {@code true} available, {@code false} not available.
    */
   public boolean isHasGoalWithApplicableRules() {
      return hasGoalWithApplicableRules;
   }

   /**
    * Defines if at least one goal with applicable rules is available.
    * @param hasGoalWithApplicableRules {@code true} available, {@code false} not available.
    */
   protected void setHasGoalWithApplicableRules(boolean hasGoalWithApplicableRules) {
      boolean oldValue = isHasGoalWithApplicableRules();
      this.hasGoalWithApplicableRules = hasGoalWithApplicableRules;
      firePropertyChange(PROP_HAS_GOAL_WITH_APPLICABLE_RULES, oldValue, isHasGoalWithApplicableRules());
   }

   /**
    * Checks if at least one goal without applicable rules is available.
    * @return {@code true} available, {@code false} not available.
    */
   public boolean isHasGoalWithoutApplicableRules() {
      return hasGoalWithoutApplicableRules;
   }

   /**
    * Defines if at least one goal without applicable rules is available.
    * @param hasGoalWithoutApplicableRules {@code true} available, {@code false} not available.
    */
   protected void setHasGoalWithoutApplicableRules(boolean hasGoalWithoutApplicableRules) {
      boolean oldValue = isHasGoalWithoutApplicableRules();
      this.hasGoalWithoutApplicableRules = hasGoalWithoutApplicableRules;
      firePropertyChange(PROP_HAS_GOAL_WITHOUT_APPLICABLE_RULES, oldValue, isHasGoalWithoutApplicableRules());
   }

   /**
     * Checks if a proof result is available.
     * @return {@code true} proof result is available, {@code false} no proof result available.
     */
    public boolean hasResult() {
        return getResult() != null && !MonKeYProofResult.UNKNOWN.equals(getResult());
    }

    /**
     * Removes the current KeY proof from the user interface.  
     * @throws InvocationTargetException Occurred Exception
     * @throws InterruptedException Occurred Exception
     */
    public void removeProof() throws InterruptedException, InvocationTargetException {
       removeProof(proof);
       proof = null;
    }
    
    /**
     * Removes the given proof from the user interface.
     * @param proofToRemove The proof to remove.
     * @throws InvocationTargetException Occurred Exception
     * @throws InterruptedException Occurred Exception
     */
    protected void removeProof(final Proof proofToRemove) throws InterruptedException, InvocationTargetException {
       if (proofToRemove != null) {
          Runnable run = new Runnable() {
             @Override
             public void run() {
                ProofUserManager.getInstance().removeUserAndDispose(proofToRemove, MonKeYProof.this);
             }
          };
          if (MonKeYUtil.isMainWindowEnvironment(environment)) {
             SwingUtil.invokeAndWait(run);
          }
          else {
             run.run();
          }
          proofToRemove.dispose();
       }
    }

   /**
    * Returns a unique file name in which this proof should be saved.
    * @return The unique file name to save proof in or {@code null} if no proof is already instantiated.
    */
    public String getProofFileName() {
        String name = contract.getName().toString() + "." + KeYUtil.PROOF_FILE_EXTENSION;
        return MiscTools.toValidFileName(name);
        // return getTypeName() + "_" + getTargetName() + "_" +
        // getContractName() + "." + KeYUtil.PROOF_FILE_EXTENSION;
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
      // Try proof loading only if proof is not already closed.
      if (!MonKeYProofResult.CLOSED.equals(getResult())) {
         if (existsProofFile(proofDirectory)) {
            IRunnableWithResult<Proof> run = new AbstractRunnableWithResult<Proof>() {
               @Override
               public void run() {
                   try {
                       final File bootClassPathFile = !StringUtil.isTrimmedEmpty(bootClassPath) ? new File(bootClassPath) : null;
                       if (MonKeYUtil.isMainWindowEnvironment(environment)) {
                          KeYUtil.runWithoutResultDialog(new KeYUtil.IRunnableWithMainWindow() {
                             @Override
                             public void run(MainWindow main) throws Exception {
                                DefaultProblemLoader loader = main.getUserInterface().load(null, new File(proofDirectory, getProofFileName()), null, bootClassPathFile);
                                setResult(loader.getProof());
                             }
                          });
                       }
                       else {
                          DefaultProblemLoader loader = environment.getUi().load(null, new File(proofDirectory, getProofFileName()), null, bootClassPathFile);
                          setResult(loader.getProof());
                       }
                   }
                   catch (Exception e) {
                       setException(e);
                   }
               }
            };
            proofStartTime = System.currentTimeMillis();
            SwingUtil.invokeAndWait(run);
            if (run.getException() != null) {
               setReuseStatus(run.getException().getMessage());
               // Try to remove proof which caused an exception during loading process
               if (run.getException() instanceof ProblemLoaderException) {
                  ProblemLoaderException ple = (ProblemLoaderException)run.getException();
                  removeProof(ple.getOrigin().getProof());
               }
            }
            else {
               proof = run.getResult();
               setReuseStatus("Loaded Proof");
               updateStatistics();
               if(proof.closed()) {
                  setResult(MonKeYProofResult.CLOSED);
                  removeProof(); // Remove closed proof to free memory
               }
               else {
                  setResult(MonKeYProofResult.OPEN);
                  // Maybe the user likes to close the proof manually, so listen for future changes
                  proof.addProofTreeListener(new ProofTreeAdapter() {
                      @Override
                      public void proofClosed(ProofTreeEvent e) {
                          handleProofClosed(e);
                      }
                  });
               }
            }
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

   /**
    * Returns the {@link Proof} instance if available.
    * @return The {@link Proof} instance if available.
    */
   public Proof getProof() {
      return proof;
   }

   /**
    * Returns the used {@link KeYEnvironment}.
    * @return The used {@link KeYEnvironment}.
    */
   public KeYEnvironment<?> getEnvironment() {
      return environment;
   }
}