package org.key_project;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.old_unused.WeatherService;
import org.key_project.prompts.Gpt3Prompt;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Example application which proves all proof obligations of the source folder 'example' using KeY.
 *
 * @author Martin Hentschel
 */
public class Main {
    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    /**
     * The program entry point.
     *
     * @param args The start parameters.
     */
    public static void main(String[] args) {
        String pwd = System.getProperty("user.dir");
        System.out.println(pwd);
        String home = System.getProperty("user.home");
        Path location = Path.of(args.length == 1 ? (args[0]) : ("./example/DemoTwo.java"));
        Path tmpFile = Path.of(home + "/uni/prak-gpt/tmp/working.java");

        String bench_folder = "/home/pat/uni/prak-gpt/data/case/";

        try {
            String token = Files.readAllLines(Path.of(home +"/.key/openai-key.txt")).get(0);
//            benchit(token, bench_folder, Benchmark.benchmarks, tmpFile);
            demo(token, location, tmpFile);
        } catch (Exception e) {
            System.out.println(e);
        }
    }

    private static void benchit(String token, String bench_folder, String[] benchmarks, Path tmpFile) {
        int maxTries = 5;
        int repeats = 15;
        List<Benchmark> bmres = new ArrayList<>();
        for(String benchClass : benchmarks) {
            try{
                var bm = Benchmark.onClass( bench_folder, benchClass, token, maxTries, tmpFile, repeats);
                if (bm != null) bmres.add(bm);
            } catch (Exception e) {
                System.err.println(e.toString());
            }
        }
        for (var bm : bmres) {
            System.out.println(bm.getRepr());
        }
    }

    private static void demo(String token, Path location, Path tmpFile) {

        try {
            List<String> classLines = Files.readAllLines(location);
            Gpt3Prompt.specifyFunction(token, classLines, "g", false, "f", false, 5, tmpFile);
        } catch (Exception e) {
            System.out.println(e);
        }
    }

    private static void old_discovery(File location) {
        KeYEnvironment<?> env = null;
        // Path to the source code folder/file or to a *.proof file
        try {
            // Ensure that Taclets are parsed
            env = Utility.createKeyEnvironment(location, null, null, null);
            ImmutableList<ProgramVariable> projectionVariables = ImmutableList.fromList(new LinkedList<>());
            List<Contract> contracts = Utility.getContracts(env);
            Utility.printMethodOfContract(contracts.get(0));
            List<UnclosedProof> unclosedProofs = Utility.tryClosingProofsAndListUnclosed(env, contracts, false, projectionVariables);
        } catch (ProblemLoaderException e) {
            LOGGER.info("Exception at '{}'", location, e);
        } finally {
            if (env != null) env.dispose();
        }
    }
}
