/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.Callable;

import org.key_project.proofmanagement.check.*;
import org.key_project.proofmanagement.io.HTMLReport;
import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.ProofBundleHandler;
import org.key_project.proofmanagement.merge.ProofBundleMerger;

import org.jspecify.annotations.Nullable;
import picocli.CommandLine;
import picocli.CommandLine.Command;
import picocli.CommandLine.Option;
import picocli.CommandLine.Parameters;

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
@Command(subcommands = { Main.BundleCommand.class, Main.CheckCommand.class,
    Main.MergeCommand.class })
public final class Main {
    private static final String check_missing_desc = "enables check for unproven contracts";
    private static final String check_settings_desc = "enables check for consistent proof settings";
    private static final String check_replay_desc =
        "enables check whether all saved proofs can be replayed successfully";
    private static final String check_dependency_desc = "enables check for cyclic dependencies";
    private static final String check_report_desc =
        "writes the report to an HTML file at the given path";
    private static final String usage_merge =
        "pm merge [--force] [--no-check] <bundle1> <bundle2> ... <output>";
    private static final String merge_force_desc =
        "Tries to merge the proof bundles even if the files check fails (may rename some files). Use only if you know what you are doing!";
    private static final String merge_check_desc =
        "Merges and performs a check if successful. The arguments are passed to check command.";


    /**
     * The check subcommand applies the selected checks to the proof bundle and generates an HTML
     * report if desired.
     */
    @Command(name = "check", description = "Checks a single proof bundle for consistency")
    public static class CheckCommand implements Callable<Integer> {
        /**
         * checks if the settings for the proofs are compatible
         */
        @Option(names = "--settings", description = "enables check for consistent proof settings")
        public boolean settings;
        /**
         * checks for unsound dependencies between contracts and proofs
         */
        @Option(names = "--dependency", description = "enables check for cyclic dependencies")
        public boolean dependency;

        /**
         * checks if there are any unproven contracts in the bundle
         */
        @Option(names = "--missing", description = "enables check for unproven contracts")
        public boolean missing;

        /**
         * checks whether the proofs in the bundle are replayable
         */
        @Option(names = "--replay", description = check_replay_desc)
        public boolean replay;
        // check.addOption("--auto", description = check_auto_desc"));
        // check.addOption("--explicit", description = check_explicit_desc"));

        /**
         * reportPath the output path for the HTML report (if selected)
         */
        @Option(names = "--report", paramLabel = "FOLDER", description = check_report_desc)
        public @Nullable Path reportPath;

        /**
         * bundlePath the path of the bundle (directory or zip file)
         */
        @Parameters(paramLabel = "FILE")
        public Path bundlePath;

        @Override
        public Integer call() throws Exception {
            // check [--settings] [--dependency] [--missing] [--replay] [--report <out_path>]
            // <bundle_path>
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
                return -1;
            } catch (ProofManagementException e) {
                globalResult.print(LogLevel.ERROR, e.getMessage());
                globalResult.print("ProofManagement interrupted due to critical error.");
                e.printStackTrace();
                return -1;
            } catch (Throwable e) {
                System.err.println("Error creating the report: ");
                e.printStackTrace();
                return -1;
            }
            return 0;
        }
    }

    @Command(name = "merge", description = "Merges multiple proof bundles")
    public static class MergeCommand implements Callable<Integer> {
        // Usually, the merging process is cancelled if there are conflicting files in both bundles.
        // This option forces merging. For the conflicting files, their versions from the first
        // bundle are taken.
        @Option(names = "--force", description = merge_force_desc)
        public boolean force;

        @Option(names = "--check", paramLabel = "STRING", description = merge_check_desc)
        public @Nullable String checkParams;

        @Option(names = { "--output", "-o" }, required = true, description = "Output file",
            paramLabel = "FILE")
        public Path output;

        // at least three files!
        @Parameters(arity = "2..*", paramLabel = "FILE")
        public List<Path> arguments = List.of();

        @Override
        public Integer call() throws Exception {
            // merge [--force] [--check "<check_args>"] <bundle1> <bundle2> ... <output>

            // at the moment only used for logging
            CheckerData logger = new CheckerData(LogLevel.DEBUG);

            try {
                ProofBundleMerger.merge(arguments, output, force, logger);
            } catch (ProofManagementException e) {
                System.err.println("Error when trying to merge the bundles: ");
                e.printStackTrace();
                return -1;
            }

            // perform a check on the newly created bundle with given commands
            if (checkParams != null) {
                // remove quotation marks
                checkParams = checkParams.substring(1, checkParams.length() - 1);
                String[] temp = checkParams.trim().split(" ");
                return new CommandLine(new CheckCommand()).execute(temp);
            }
            return 0;
        }
    }

    /**
     * TODO: bundle subcommand, which zips a directory into a proof bundle (and may perform checks)
     * // bundle [-c|--check "check_options"] <root_dir> <bundle_path>
     */
    @Command(name = "bundle",
        description = "Creates a zipped proof bundle (file extension \"zproof\") from a directory following the proof bundle path rules.")
    static class BundleCommand implements Callable<Integer> {
        @Parameters(arity = "2..*")
        public List<Path> arguments = List.of();

        @Override
        public Integer call() throws Exception {
            System.out.println("todo not implemented yet");
            return 0;
        }
    }

    Main() {
    }

    /**
     * Main entry point for ProofManagement.
     *
     * @param args the commandline arguments. See class JavaDoc for a detailed description.
     */
    public static void main(String[] args) {
        new CommandLine(new Main()).execute(args);
    }

    private static void generateReport(CheckerData globalResult, Path reportPath) {
        try {
            HTMLReport.print(globalResult, reportPath);
        } catch (IOException e) {
            System.err.println("Error creating the report: ");
            e.printStackTrace();
        }
    }
}
