package de.uka.ilkd.key.symbolic_execution.util;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * Instances of this class are used to collect and access all
 * relevant information for symbolic execution tree extraction of {@link Proof}s
 * via an {@link SymbolicExecutionTreeBuilder}.
 * @author Martin Hentschel
 */
public class SymbolicExecutionEnvironment<U extends UserInterface> {
   /**
    * The {@link UserInterface} in which the {@link Proof} is loaded.
    */
   private U ui;
   
   /**
    * The loaded project.
    */
   private InitConfig initConfig;
   
   /**
    * The {@link SymbolicExecutionTreeBuilder} for execution tree extraction.
    */
   private SymbolicExecutionTreeBuilder builder;

   /**
    * Constructor.
    * @param ui The {@link UserInterface} in which the {@link Proof} is loaded.
    * @param initConfig The loaded project.
    * @param builder The {@link SymbolicExecutionTreeBuilder} for execution tree extraction.
    */
   public SymbolicExecutionEnvironment(U ui,
                                       InitConfig initConfig, 
                                       SymbolicExecutionTreeBuilder builder) {
      this.ui = ui;
      this.initConfig = initConfig;
      this.builder = builder;
   }

   /**
    * Returns the {@link UserInterface} in which the {@link Proof} is loaded.
    * @return The {@link UserInterface} in which the {@link Proof} is loaded.
    */
   public U getUi() {
      return ui;
   }

   /**
    * Returns the loaded project.
    * @return The loaded project.
    */
   public InitConfig getInitConfig() {
      return initConfig;
   }

   /**
    * Returns the {@link Services} of {@link #getInitConfig()}.
    * @return The {@link Services} of {@link #getInitConfig()}.
    */
   public Services getServices() {
      return initConfig.getServices();
   }

   /**
    * Returns the {@link SymbolicExecutionTreeBuilder} for execution tree extraction.
    * @return The {@link SymbolicExecutionTreeBuilder} for execution tree extraction.
    */
   public SymbolicExecutionTreeBuilder getBuilder() {
      return builder;
   }
   
   /**
    * Returns the {@link Proof} of {@link #getBuilder()}.
    * @return The {@link Proof} of {@link #getBuilder()}.
    */
   public Proof getProof() {
      return getBuilder().getProof();
   }
   
   /**
    * Configures the given {@link Proof} to use the symbolic execution strategy.
    * @param proof The {@link Proof} to configure.
    * @param maximalNumberOfNodesPerBranch The maximal number of nodes per branch.
    */
   public static void configureProofForSymbolicExecution(Proof proof, int maximalNumberOfNodesPerBranch) {
      if (proof != null) {
         StrategyProperties strategyProperties = SymbolicExecutionStrategy.getSymbolicExecutionStrategyProperties(true, false, false, true);
         proof.setActiveStrategy(new SymbolicExecutionStrategy.Factory().create(proof, strategyProperties));
         proof.getSettings().getStrategySettings().setCustomApplyStrategyGoalChooser(new SymbolicExecutionGoalChooser());
         proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(new ExecutedSymbolicExecutionTreeNodesStopCondition(maximalNumberOfNodesPerBranch));
      }
   }
}
