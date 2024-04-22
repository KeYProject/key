package org.key_project;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.HeapSimplificationMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.MiscTools;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import javax.annotation.Nullable;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

public final class Utility {
    public static void appendToFile(String filename, String s) {
        try
        {
            FileWriter fw = new FileWriter(filename,true); //the true will append the new data
            fw.write(s);
            fw.write("\n");//appends the string to the file
            fw.close();
        } catch(IOException ioe)
        {
            System.err.println("IOException: " + ioe.getMessage());
        }
    }

    static final int MAX_STEPS = 50000;
    /**
     * Creates a KeY environment loading the given file
     *
     * @param location Input File
     * @return A new KeY environment
     * @throws ProblemLoaderException FIle could not be loaded
     */
    public static KeYEnvironment<?> createKeyEnvironment(
        File location,
        List<File> classPaths,
        File bootClassPath,
        List<File> includes) throws ProblemLoaderException {
        // Ensure that Taclets are parsed
        if (!ProofSettings.isChoiceSettingInitialised()) {
            System.out.println("Trying to load "+location.getAbsolutePath());
            KeYEnvironment<?>
                    env = KeYEnvironment.load(location, classPaths, bootClassPath, includes);

            env.dispose();
        }
        // Set Taclet options
        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        Map<String, String> oldSettings = choiceSettings.getDefaultChoices();
        HashMap<String, String> newSettings = new HashMap<>(oldSettings);
        newSettings.putAll(MiscTools.getDefaultTacletOptions());
        choiceSettings.setDefaultChoices(newSettings);
        // Load source code
        KeYEnvironment<?> env = KeYEnvironment.load(location, classPaths, bootClassPath, includes);
        // env.getLoadedProof() returns performed proof if a *.proof file is loaded
        return env;
    }

    public static List<Contract> getContracts(KeYEnvironment<?> env) {
        // List all specifications of all types in the source location (not classPaths and
        // bootClassPath)
        final List<Contract> proofContracts = new LinkedList<>();
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
        return proofContracts;
    }

    private static Proof createProofAndTryClosing(KeYEnvironment<?> env, Contract contract) throws ProofInputException, Exception {
        Proof proof =
                env.createProof(contract.createProofObl(env.getInitConfig(), contract));
        // Set proof strategy options
        StrategyProperties sp =
                proof.getSettings().getStrategySettings().getActiveStrategyProperties();
        // We want to use method contracts instead of expanding the method
        sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
                StrategyProperties.METHOD_CONTRACT);
        sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY,
                StrategyProperties.DEP_ON);
        sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
                StrategyProperties.QUERY_ON);
        sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
                StrategyProperties.NON_LIN_ARITH_DEF_OPS);
        // Important: We want to unroll the proof as much as possible and not stop at the first unclosable goal!
        sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY,
                StrategyProperties.STOPMODE_DEFAULT);
        proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
        // Make sure that the new options are used
        int maxSteps = MAX_STEPS;
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxSteps);
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                .setActiveStrategyProperties(sp);
        proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
        //AbstractProofMacro autopilot = new FullAutoPilotProofMacro();
        //autopilot.applyTo(env.getUi(), proof.root(), null, null);
        proof.setActiveStrategy(proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));
        // Start auto mode
        env.getUi().getProofControl().startAndWaitForAutoMode(proof);
        AbstractProofMacro closeProvable = new TryCloseMacro();
        // Close Closables
        closeProvable.applyTo(env.getUi(), proof.root(), null, null);
        // Simplify heaps
        HeapSimplificationMacro heapSimplifier = new HeapSimplificationMacro();
        heapSimplifier.applyTo(env.getUi(), proof.root(), null, null);
        // Resolve Variables through ApplyEqReverse
        Strategy strat = proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp);
        proof.setActiveStrategy(strat);
//                    proof.setActiveStrategy(new ResolveIntermediateVariablesStrategy(projectionVariablesList));
        env.getUi().getProofControl().startAndWaitForAutoMode(proof);
        // Simplify heaps again
        heapSimplifier.applyTo(env.getUi(), proof.root(), null, null);
        // Close Closables
        closeProvable.applyTo(env.getUi(), proof.root(), null, null);

        return proof;
    }

    private static boolean canThrowAwayProof(
        List<UnclosedProof> unclosedProofs,
        ImmutableList<ProgramVariable> projectionVariablesList,
        Contract contract,
        Proof proof) {
        boolean closed = proof.openGoals().isEmpty();
        if (!closed) {
            if (projectionVariablesList != null) {
                unclosedProofs.add(
                    new UnclosedProof(proof, projectionVariablesList)
                );
            } else {
                unclosedProofs.add(
                    new UnclosedProof(proof, contract.getOrigVars().params)
                );
            }
        }
        return closed;
    }

    public static List<UnclosedProof> tryClosingProofsAndListUnclosed(
        KeYEnvironment<?> env,
        List<Contract> proofContracts,
        boolean loadProofFile,
        ImmutableList<ProgramVariable> projectionVariablesList) {
        // TODO(steuber): We probably want to adjust this a little? Or make it configurable...
        List<UnclosedProof> unclosedProofs = new LinkedList<>();
        if (loadProofFile) {
            Proof curProof = env.getLoadedProof();
            if (!curProof.openGoals().isEmpty()) {
                unclosedProofs.add(
                    new UnclosedProof(curProof, projectionVariablesList)
                );
            }
            return unclosedProofs;
        } else {
            // List all specifications of all types in the source location (not classPaths and bootClassPath)
            // Perform proofs
            for (Contract contract : proofContracts) {
                Proof proof = null;
                try {
                    // Create proof
                    proof = createProofAndTryClosing(env, contract);
                    // Show proof result

                } catch (ProofInputException e) {
                    System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
                    e.printStackTrace();
                } catch (Exception e) {
                    e.printStackTrace();
                } finally {
                    if (proof != null && canThrowAwayProof(unclosedProofs, projectionVariablesList, contract, proof)) {
                        proof.dispose(); // Ensure always that all instances of Proof are disposed
                    }
                }
            }
        }
        return unclosedProofs;
    }

    public static void printMethodOfContract(Contract contract) {
        FunctionalOperationContractImpl foc = (FunctionalOperationContractImpl)contract;
        ProgramMethod pm = (ProgramMethod)foc.pm; // todo: access this without having to change the thingy to 'public'
        PositionInfo pi = pm.getPositionInfo();
        var startL = pi.getStartPosition().line();
        var endL = pi.getEndPosition().line();
        var file = pi.getURI();
        try {
            var lines = Files.readAllLines(Path.of(file));
            var toPrint = lines.stream().skip(startL-1).limit(endL - startL + 1).collect(Collectors.joining("\n"));
            System.out.println(toPrint);
        } catch (Exception e) {

        }
    }
}
