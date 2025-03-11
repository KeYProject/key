/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.ResourceBundle;

import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;

import org.key_project.proofmanagement.check.*;
import org.key_project.proofmanagement.io.HTMLReport;
import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.ProofBundleHandler;
import org.key_project.proofmanagement.merge.ProofBundleMerger;

/**
 * This is the starting class for ProofManagement.
 * <br>
 * CLI commands:
 * check [--settings] [--dependency] [--report <out_path>] <bundle_path>
 * options:
 * --settings settings check
 * --dependency dependency check
 * --auto try to use automode to close open proofs
 * --explicit (implies --auto) stores automatically found proofs explicitly as files
 * --report generate html report, needs the target filename as parameter
 * --missing check for contracts that have no proof
 * checks that are always enabled:
 * - check for duplicate proofs of the same contracts
 * individually and independently trigger different checks
 * merge [--force] [--no-check] <bundle1> <bundle2> ... <output>
 * Merges the given n bundles into a single bundle. By default, no consistency checks are run
 * (note that this may produce a completely broken bundle, if there are inconsistencies).
 * options:
 * --force merge the bundles even when the consistency check failed
 * --check "<check_options>" passes the given options to the check command and
 * executes it
 * bundle [--check]
 * options:
 * --check "<check_options>" passes the given options to the check command and
 * executes it
 *
 * @author Wolfram Pfeifer
 */
public final class Main {
    /** resource bundle where the description strings for the CLI are stored */
    private static final ResourceBundle STRINGS = ResourceBundle.getBundle("strings");

    /** usage string for general pm command */
    private static final String USAGE = STRINGS.getString("usage");

    /** usage string for check subcommand */
    private static final String USAGE_CHECK = STRINGS.getString("usage_check");

    /** usage string for merge subcommand */
    private static final String USAGE_MERGE = STRINGS.getString("usage_merge");

    /** main command line of proof management */
    private static final CommandLine CL;

    /** subcommandline for the check commmand */
    private static final CommandLine CL_MERGE;

    /** subcommandline for the merge commmand */
    private static final CommandLine CL_CHECK;

    /** subcommandline of merge (used as a hack for forwarding check options) */
    private static final CommandLine CL_MERGE_CHECK;

    static {
        // TODO: check todos in CommandLine class
        CL = new CommandLine();
        CL.setLineLength(Integer.MAX_VALUE);
        CL.addText(USAGE, false);
        CL_CHECK = CL.addSubCommand("check");
        CL_CHECK.addText(USAGE_CHECK, false);
        CL_CHECK.addOption("--settings", null, STRINGS.getString("check_settings_desc"));
        CL_CHECK.addOption("--dependency", null, STRINGS.getString("check_dependency_desc"));
        CL_CHECK.addOption("--missing", null, STRINGS.getString("check_missing_desc"));
        CL_CHECK.addOption("--replay", null, STRINGS.getString("check_replay_desc"));
        // check.addOption("--auto", null, STRINGS.getString("check_auto_desc"));
        // check.addOption("--explicit", null, STRINGS.getString("check_explicit_desc"));
        CL_CHECK.addOption("--report", "out_path", STRINGS.getString("check_report_desc"));

        CL_MERGE = CL.addSubCommand("merge");
        CL_MERGE.addText(USAGE_MERGE, false);
        CL_MERGE.addOption("--force", null, STRINGS.getString("merge_force_desc"));
        CL_MERGE.addOption("--check", "check_arguments", STRINGS.getString("merge_check_desc"));

        // enable check option forwarding for merge command
        CL_MERGE_CHECK = CL_MERGE.addSubCommand("check");
        CL_MERGE_CHECK.addOption("--settings", null, STRINGS.getString("check_settings_desc"));
        CL_MERGE_CHECK.addOption("--dependency", null, STRINGS.getString("check_dependency_desc"));
        CL_MERGE_CHECK.addOption("--missing", null, STRINGS.getString("check_missing_desc"));
        CL_MERGE_CHECK.addOption("--replay", null, STRINGS.getString("check_replay_desc"));
        // CL_MERGE_CHECK.addOption("--auto", null, STRINGS.getString("check_auto_desc"));
        // CL_MERGE_CHECK.addOption("--explicit", null, STRINGS.getString("check_explicit_desc"));
        CL_MERGE_CHECK.addOption("--report", "out_path", STRINGS.getString("check_report_desc"));

        // TODO: bundle subcommand
        // CL.addSubCommand("bundle");
    }

    private Main() {
    }

    /**
     * Main entry point for ProofManagement.
     *
     * @param args the commandline arguments. See class JavaDoc for a detailed description.
     */
    public static void main(String[] args) {
        try {
            CL.parse(args);
            if (CL.subCommandUsed("check")) {
                check(CL_CHECK);
            } else if (CL.subCommandUsed("merge")) {
                merge();
            } else {
                CL.printUsage(System.out);
            }
        } catch (CommandLineException e) {
            if (CL.subCommandUsed("check")) {
                CL_CHECK.printUsage(System.out);
            } else if (CL.subCommandUsed("merge")) {
                CL_MERGE.printUsage(System.out);
            } else {
                CL.printUsage(System.out);
            }
        }
    }

    // TODO: bundle subcommand, which zips a directory into a proof bundle (and may perform checks)
    // bundle [-c|--check "check_options"] <root_dir> <bundle_path>
    /*
     * private static void bundle(CommandLine commandLine) {
     *
     * List<String> arguments = commandLine.getArguments();
     * if (arguments.size() != 2) {
     * commandLine.printUsage(System.out);
     * }
     * }
     */

    /**
     * The check subcommand applies the selected checks to the proof bundle and generates an HTML
     * report if desired.
     *
     * @param missing checks if there are any unproven contracts in the bundle
     * @param settings checks if the settings for the proofs are compatible
     * @param replay checks whether the proofs in the bundle are replayable
     * @param dependency checks for unsound dependencies between contracts and proofs
     * @param bundlePath the path of the bundle (directory or zip file)
     * @param reportPath the output path for the HTML report (if selected)
     */
    public static void check(boolean missing, boolean settings, boolean replay, boolean dependency,
            Path bundlePath, Path reportPath) {

        // we accumulate results in this variable
        CheckerData globalResult = new CheckerData(LogLevel.DEBUG);
        try (ProofBundleHandler pbh = ProofBundleHandler.createBundleHandler(bundlePath)) {

            globalResult.setPbh(pbh);

            // add file tree to result
            globalResult.setFileTree(pbh.getFileTree());

            if (missing) {
                new MissingProofsChecker().check(pbh, globalResult);
            }
            if (settings) {
                new SettingsChecker().check(pbh, globalResult);
            }
            if (replay) {
                new ReplayChecker().check(pbh, globalResult);
            }
            if (dependency) {
                new DependencyChecker().check(pbh, globalResult);
            }
            globalResult.print("All checks done!");
            globalResult.print("Global result: " + globalResult.getGlobalState());

            // generate report
            if (reportPath != null) {
                generateReport(globalResult, reportPath);
            }
        } catch (IOException e) {
            globalResult.print(LogLevel.ERROR, e.getMessage());
            globalResult.print("Error while accessing the proof bundle!");
            globalResult.print("ProofManagement interrupted due to critical error.");
            e.printStackTrace();
        } catch (ProofManagementException e) {
            globalResult.print(LogLevel.ERROR, e.getMessage());
            globalResult.print("ProofManagement interrupted due to critical error.");
            e.printStackTrace();
        } catch (Throwable e) {
            System.err.println("Error creating the report: ");
            e.printStackTrace();
        }
    }

    private static void generateReport(CheckerData globalResult, Path reportPath) {
        try {
            HTMLReport.print(globalResult, reportPath);
        } catch (IOException e) {
            System.err.println("Error creating the report: ");
            e.printStackTrace();
        }
    }

    // check [--settings] [--dependency] [--missing] [--replay] [--report <out_path>] <bundle_path>
    private static void check(CommandLine commandLine) {
        List<String> arguments = commandLine.getArguments();
        if (arguments.size() != 1) {
            commandLine.printUsage(System.out);
            return;
        }

        Path reportPath = null;
        if (commandLine.isSet("--report")) {
            String outFileName = commandLine.getString("--report", "");
            reportPath = Paths.get(outFileName).toAbsolutePath();
        }

        String pathStr = arguments.get(0);
        Path bundlePath = Paths.get(pathStr);
        check(commandLine.isSet("--missing"), commandLine.isSet("--settings"),
            commandLine.isSet("--replay"), commandLine.isSet("--dependency"),
            bundlePath, reportPath);
    }

    // merge [--force] [--check "<check_args>"] <bundle1> <bundle2> ... <output>
    private static void merge() {
        List<String> arguments = CL_MERGE.getArguments();

        // at least three files!
        if (arguments.size() < 3) {
            CL_MERGE.printUsage(System.out);
            return;
        }

        // at the moment only used for logging
        CheckerData logger = new CheckerData(LogLevel.DEBUG);

        // convert Strings to Paths (for input and output)
        List<Path> inputs = new ArrayList<>();
        for (int i = 0; i < arguments.size() - 1; i++) {
            inputs.add(Paths.get(arguments.get(i)));
        }
        Path output = Paths.get(arguments.get(arguments.size() - 1));

        // Usually, the merging process is cancelled if there are conflicting files in both bundles.
        // This option forces merging. For the conflicting files, their versions from the first
        // bundle are taken.
        boolean force = CL_MERGE.isSet("--force");

        try {
            ProofBundleMerger.merge(inputs, output, force, logger);
        } catch (ProofManagementException e) {
            System.err.println("Error when trying to merge the bundles: ");
            e.printStackTrace();
            return;
        }

        // perform a check on the newly created bundle with given commands
        if (CL_MERGE.isSet("--check")) {
            String checkParams = CL_MERGE.getString("--check", "");

            // remove quotation marks
            checkParams = checkParams.substring(1, checkParams.length() - 1);
            String[] temp = checkParams.trim().split(" ");

            String[] newArgs = Arrays.copyOfRange(temp, 0, temp.length + 1);
            newArgs[newArgs.length - 1] = output.toString();
            try {
                CL_MERGE_CHECK.parse(newArgs);
                check(CL_MERGE_CHECK);
            } catch (CommandLineException e) {
                e.printStackTrace();
            }
        }

    }
}
