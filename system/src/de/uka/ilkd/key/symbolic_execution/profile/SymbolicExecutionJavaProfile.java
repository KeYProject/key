package de.uka.ilkd.key.symbolic_execution.profile;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.label.ITermLabelWorker;
import de.uka.ilkd.key.rule.label.LoopBodyTermLabelInstantiator;
import de.uka.ilkd.key.rule.label.LoopInvariantNormalBehaviorTermLabelInstantiator;
import de.uka.ilkd.key.rule.label.SymbolicExecutionTermLabelInstantiator;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.symbolic_execution.rule.ModalitySideProofRule;
import de.uka.ilkd.key.symbolic_execution.rule.QuerySideProofRule;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;

/**
 * An extended {@link JavaProfile} used by the symbolic execution API.
 * @author Martin Hentschel
 */
public class SymbolicExecutionJavaProfile extends JavaProfile {
   /**
    * The {@link Name} of this {@link Profile}.
    */
   public static final String NAME = "Java Profile for Symbolic Execution";
   
   /**
    * The used {@link StrategyFactory} of the {@link SymbolicExecutionStrategy}.
    */
   private final static StrategyFactory SYMBOLIC_EXECUTION_FACTORY = new SymbolicExecutionStrategy.Factory();
   
   /**
    * <p>
    * The default instance of this class.
    * </p>
    * <p> 
    * It is typically used in the {@link Thread} of the user interface.
    * Other instances of this class are typically only required to 
    * use them in different {@link Thread}s (not the UI {@link Thread}).
    * </p>
    */
   public static SymbolicExecutionJavaProfile defaultInstance; 

   /**
    * Constructor.
    */
   public SymbolicExecutionJavaProfile() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ImmutableList<ITermLabelWorker> computeLabelInstantiators() {
      ImmutableList<ITermLabelWorker> result = super.computeLabelInstantiators();
      result = result.prepend(getSymbolicExecutionLabelInstantiators());
      return result;
   }
   
   /**
    * Returns the special {@link ITermLabelWorker} used for symbolic execution-
    * @return The special {@link ITermLabelWorker} used for symbolic execution-
    */
   public static ImmutableList<ITermLabelWorker> getSymbolicExecutionLabelInstantiators() {
      ImmutableList<ITermLabelWorker> result = ImmutableSLList.nil();
      result = result.prepend(SymbolicExecutionTermLabelInstantiator.INSTANCE);
      result = result.prepend(LoopBodyTermLabelInstantiator.INSTANCE);
      result = result.prepend(LoopInvariantNormalBehaviorTermLabelInstantiator.INSTANCE);
      return result;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected ImmutableSet<StrategyFactory> getStrategyFactories() {
      ImmutableSet<StrategyFactory> set = super.getStrategyFactories();
      set = set.add(SYMBOLIC_EXECUTION_FACTORY);
      return set;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected ImmutableList<BuiltInRule> initBuiltInRules() { 
      ImmutableList<BuiltInRule> builtInRules = super.initBuiltInRules();
      builtInRules = builtInRules.prepend(QuerySideProofRule.INSTANCE);
      builtInRules = builtInRules.prepend(ModalitySideProofRule.INSTANCE);
      return builtInRules;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String name() {
      return NAME;
   }

   /**
    * <p>
    * Returns the default instance of this class.
    * </p>
    * <p>
    * It is typically used in the {@link Thread} of the user interface.
    * Other instances of this class are typically only required to 
    * use them in different {@link Thread}s (not the UI {@link Thread}).
    * </p>
    * @return The default instance for usage in the {@link Thread} of the user interface.
    */
   public static synchronized SymbolicExecutionJavaProfile getDefaultInstance() {
       if (defaultInstance == null) {
           defaultInstance = new SymbolicExecutionJavaProfile();
       }
      return defaultInstance;
   }
}
