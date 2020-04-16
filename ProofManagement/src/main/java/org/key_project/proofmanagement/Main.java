package org.key_project.proofmanagement;
    // TODO: the checkstyle regex for package name does neither allow proof_management nor proofManagement
    // Is this intended?

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;
import org.key_project.proofmanagement.check.*;
import org.key_project.proofmanagement.io.ProofBundleHandler;
import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.report.Report;
import org.key_project.proofmanagement.merge.ProofBundleMerger;

/**
 * This is the starting class for ProofManagement.
 * <br>
 * CLI commands:
 *  check [-s|--settings] [-d|--dependency] [-r|--report <out_path>] <bundle_path>
 *    options:
 *        -s --settings settings check
 *        -d --dependency dependency check
 *        -a --auto try to use automode to close open proofs
 *        -e --explicit (implies a) stores automatically found proofs explicitly as files
 *        -r --report generate html report + API
 *        -c --completion check for completion state (have all POs been proven?)
 *    checks that are always enabled:
 *        - check for duplicate proofs of the same contracts
 *    individually and independently trigger different checks
 *  merge [-f|--force] [-n|--no-check] <bundle1> <bundle2> ... <output>
 *    options:
 *        -f --force merge the bundles even when the consistency check failed
 *        -c --check "<check_options>" passes the given options to the check command and
 *                  executes it
 *  bundle [-c|--check]
 *    options:
 *        -c --check "<check_options>" passes the given options to the check command and
 *                  executes it
 *
 * @author Wolfram Pfeifer
 */
public final class Main {
    /** usage string for general pm command */
    private static final String USAGE = "Usage: pm <command>" + System.lineSeparator()
        + System.lineSeparator() + "available commands:" + System.lineSeparator()
        + "    check: Checks a single proof bundle for consistency." + System.lineSeparator()
        + "    merge: Merges two proof bundles." + System.lineSeparator();

    /** usage string for check subcommand */
    private static final String USAGE_CHECK =
        "pm check [-s|--settings] [-d|--dependency] [-f|--files] [-r|--report <out_path>]" +
            "<bundle_path>" + System.lineSeparator();

    /** usage string for merge subcommand */
    private static final String USAGE_MERGE =
        "pm merge [-f|--force] [-n|--no-check] <bundle1> <bundle2> ... <output>"
            + System.lineSeparator();

    /** command line of proof management */
    private static final CommandLine CL;

    static {
        // TODO: check todos in CommandLine class
        CL = new CommandLine();
        CL.addSubCommand("check");
        CommandLine check = CL.getSubCommandLine("check");
        check.addOption("--settings", null, "Enables check for consistent proof settings");
        check.addOption("--dependency", null, "Enables check for cyclic dependencies");
        check.addOption("--files", null, "Enables check for compatible files");
        check.addOption("--missing", null, "Enables check whether there are unproven contracts.");
        check.addOption("--replay", null, "Enables check whether all saved proofs can be replayed successfully.");
        check.addOption("--auto", null, "Tries to run automatic proof search for all unproven contracts.");
        check.addOption("--explicit", null, "Makes automatically found proofs explicit (implies --auto).");
        check.addOption("--report", "out_path", "Writes the report to a HTML file at the given path");

        CL.addSubCommand("merge");
        CommandLine merge = CL.getSubCommandLine("merge");
        merge.addOption("--force", null, "Tries to merge the proof bundles even if the files check fails (may rename some files). Only use if you know what you are doing!");
        merge.addOption("--check", "check_arguments", "Performs a check after successful merge. The arguments are passed too check");

        // enable check option forwarding for merge command
        merge.addSubCommand("check");
        CommandLine mergeCheck = merge.getSubCommandLine("check");
        mergeCheck.addOption("--settings", null, "Enables check for consistent proof settings");
        mergeCheck.addOption("--dependency", null, "Enables check for cyclic dependencies");
        mergeCheck.addOption("--files", null, "Enables check for compatible files");
        mergeCheck.addOption("--report", "out_path", "Writes the report to a HTML file at the given path");

        // TODO: bundle subcommand
        CL.addSubCommand("bundle");
    }

    private Main() {
    }

    /**
     * Main entry point for ProofManagement.
     * @param args the commandline arguments. See class JavaDoc for a detailed description.
     */
    public static void main(String[] args) {
        try {
            CL.parse(args);
            if (CL.subCommandUsed("check")) {
                check(CL.getSubCommandLine("check"));
            } else if (CL.subCommandUsed("merge")) {
                merge(CL.getSubCommandLine("merge"));
            } else if (CL.subCommandUsed("bundle")) {
                bundle(CL.getSubCommandLine("bundle"));
            }
        } catch (CommandLineException e) {
            e.printStackTrace();
        }
    }

    // bundle [-c|--check "check_options"] <root_dir> <bundle_path>
    private static void bundle(CommandLine commandLine) {
        // TODO: bundle subcommand

        List<String> arguments = commandLine.getArguments();
        if (arguments.size() != 2) {
            commandLine.printUsage(System.out);
        }
    }

    // check [-s|--settings] [-d|--dependency] [-f|--files] [-r|--report <out_path>] <bundle_path>
    private static void check(CommandLine commandLine) {

        List<String> arguments = commandLine.getArguments();
        if (arguments.size() != 1) {
            commandLine.printUsage(System.out);
        }

        // we accumulate results in this variable
        CheckerData globalResult = new CheckerData(LogLevel.DEBUG);
        Path bundlePath = Paths.get(arguments.get(0));
        try (ProofBundleHandler pbh = ProofBundleHandler.createBundleHandler(bundlePath)) {

            try {
                List<Path> proofFiles = pbh.getProofFiles();

                globalResult.setConsistent(true);   // should be implicit
                globalResult.setPbh(pbh);

                // add file tree to result
                globalResult.setFileTree(pbh.getFileTree());

                try {
                    if (commandLine.isSet("--missing")) {
                        new MissingProofsChecker().check(proofFiles, globalResult);
                    }
                    if (commandLine.isSet("--settings")) {
                        new SettingsChecker().check(proofFiles, globalResult);
                    }
                    if (commandLine.isSet("--dependency")) {
                        new DependencyChecker().check(proofFiles, globalResult);
                    }
                    if (commandLine.isSet("--replay")) {
                        new ReplayChecker().check(proofFiles, globalResult);
                    }
                    globalResult.print("All checks done!");
                    globalResult.print("Global result: ");
                } catch (ProofManagementException e) {
                    globalResult.print(LogLevel.ERROR, e.getMessage());
                    globalResult.print("ProofManagment interrupted due to critical error.");
                    globalResult.print("Generating report.");
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
        } catch (Exception e) {
            e.printStackTrace();
        }

        // TODO: print overall report
        //  proven contracts
        //  contracts proven but missing dependencies
        //  unproven
        //  different settings

        if (commandLine.isSet("--report")) {
            String outFileName = commandLine.getString("--report", "");
            Path output = Paths.get(outFileName).toAbsolutePath();
            Report report = new Report(globalResult);
            report.setOutPath(output);
            try {
                report.printReport();
            } catch (IOException | URISyntaxException e) {
                System.err.println("Error creating the report: ");
                e.printStackTrace();
            }
        }
    }

    // merge [-f|--force] [-n|--no-check] [--check "<check_args>"] <bundle1> <bundle2> ... <output>
    private static void merge(CommandLine commandLine) {
        List<String> arguments = commandLine.getArguments();

        // at least three files!
        if (arguments.size() < 3) {
            commandLine.printUsage(System.out);
        }

        // convert Strings to Paths (for input and output)
        List<Path> inputs = new ArrayList<>();
        for (int i = 0; i < arguments.size() - 1; i++) {
            inputs.add(Paths.get(arguments.get(i)));
        }
        Path output = Paths.get(arguments.get(arguments.size() - 1));

        if (commandLine.isSet("--force")) {
            // TODO:
        }

        // TODO: use result, print message, clean up particularly created zips
        ProofBundleMerger.merge(inputs, output);

        // perform a check with given commands
        if (commandLine.isSet("--check")) {
            String[] temp = commandLine.getString("--check", "").trim().split(" ");
            String[] newArgs = Arrays.copyOfRange(temp, 0,temp.length + 1);
            newArgs[newArgs.length - 1] = output.toString();
            try {
                CommandLine checkCommandLine = commandLine.getSubCommandLine("check");
                checkCommandLine.parse(newArgs);
                check(checkCommandLine);
            } catch (CommandLineException e) {
                e.printStackTrace();
            }
        }

    }
}
