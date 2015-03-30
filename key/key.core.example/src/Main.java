import java.io.File;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Example application which proves all proof obligations of
 * the source folder 'example' using KeY.
 * @author Martin Hentschel
 */
public class Main {
   /**
    * The program entry point.
    * @param args The start parameters.
    */
   public static void main(String[] args) {
      File location = args.length == 1  ?
                      new File(args[0]) :
                      new File("example"); // Path to the source code folder/file or to a *.proof file
      List<File> classPaths = null; // Optionally: Additional specifications for API classes
      File bootClassPath = null; // Optionally: Different default specifications for Java API
      try {
         // Ensure that Taclets are parsed
         if (!ProofSettings.isChoiceSettingInitialised()) {
            KeYEnvironment<?> env = KeYEnvironment.load(location, classPaths, bootClassPath);
            env.dispose();
         }
         // Set Taclet options
         ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
         HashMap<String, String> oldSettings = choiceSettings.getDefaultChoices();
         HashMap<String, String> newSettings = new HashMap<String, String>(oldSettings);
         newSettings.putAll(MiscTools.getDefaultTacletOptions());
         choiceSettings.setDefaultChoices(newSettings);
         // Load source code
         KeYEnvironment<?> env = KeYEnvironment.load(location, classPaths, bootClassPath); // env.getLoadedProof() returns performed proof if a *.proof file is loaded
         try {
            // List all specifications of all types in the source location (not classPaths and bootClassPath)
            final List<Contract> proofContracts = new LinkedList<Contract>();
            Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
            for (KeYJavaType type : kjts) {
               if (!KeYTypeUtil.isLibraryClass(type)) {
                  ImmutableSet<IObserverFunction> targets = env.getSpecificationRepository().getContractTargets(type);
                  for (IObserverFunction target : targets) {
                     ImmutableSet<Contract> contracts = env.getSpecificationRepository().getContracts(type, target);
                     for (Contract contract : contracts) {
                        proofContracts.add(contract);
                     }
                  }
               }
            }
            // Perform proofs
            for (Contract contract : proofContracts) {
               Proof proof = null;
               try {
                  // Create proof
                  proof = env.createProof(contract.createProofObl(env.getInitConfig(), contract));
                  // Set proof strategy options
                  StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
                  sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_CONTRACT);
                  sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_ON);
                  sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_ON);
                  sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
                  sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
                  proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
                  // Make sure that the new options are used
                  int maxSteps = 10000;
                  ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxSteps);
                  ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
                  proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
                  proof.setActiveStrategy(proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));
                  // Start auto mode
                  env.getUi().getProofControl().startAndWaitForAutoMode(proof);
                  // Show proof result
                  boolean closed = proof.openGoals().isEmpty();
                  System.out.println("Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is " + (closed ? "verified" : "still open") + ".");
               }
               catch (ProofInputException e) {
                  System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
                  e.printStackTrace();
               }
               finally {
                  if (proof != null) {
                     proof.dispose(); // Ensure always that all instances of Proof are disposed
                  }
               }
            }
         }
         finally {
            env.dispose(); // Ensure always that all instances of KeYEnvironment are disposed
         }
      }
      catch (ProblemLoaderException e) {
         System.out.println("Exception at '" + location + "':");
         e.printStackTrace();
      }
   }
}
