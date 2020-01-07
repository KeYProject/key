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
import java.util.zip.ZipException;

import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;
import org.key_project.proofmanagement.check.CheckerData;
import org.key_project.proofmanagement.check.DependencyChecker;
import org.key_project.proofmanagement.check.MissingProofsChecker;
import org.key_project.proofmanagement.check.SettingsChecker;
import org.key_project.proofmanagement.io.ProofBundleHandler;
import org.key_project.proofmanagement.io.report.Report;
import org.key_project.proofmanagement.merge.ProofBundleMerger;

public class Main {

    /* CLI commands:
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
     */

    private static final String USAGE = "Usage: pm <command>" + System.lineSeparator()
        + System.lineSeparator() + "available commands:" + System.lineSeparator()
        + "    check: Checks a single proof bundle for consistency." + System.lineSeparator()
        + "    merge: Merges two proof bundles." + System.lineSeparator();

    private static final String USAGE_CHECK =
        "pm check [-s|--settings] [-d|--dependency] [-f|--files] [-r|--report <out_path>]" +
            "<bundle_path>" + System.lineSeparator();

    private static final String USAGE_MERGE =
        "pm merge [-f|--force] [-n|--no-check] <bundle1> <bundle2> ... <output>"
            + System.lineSeparator();

    private static CommandLine setUpCL() {
        CommandLine cl = new CommandLine();
        cl.addSubCommand("check");
        CommandLine check = cl.getSubCommandLine("check");
        check.addOption("--settings", null, "Enables check for consistent proof settings");
        check.addOption("--dependency", null, "Enables check for cyclic dependencies");
        check.addOption("--files", null, "Enables check for compatible files");
        check.addOption("--missing", null, "Enables check whether there are unproven contracts.");
        check.addOption("--replay", null, "Enables check whether all saved proofs can be replayed successfully.");
        check.addOption("--auto", null, "Tries to run automatic proof search for all unproven contracts.");
        check.addOption("--explicit", null, "Makes automatically found proofs explicit (implies --auto).");
        check.addOption("--report", "out_path", "Writes the report to a HTML file at the given path");

        cl.addSubCommand("merge");
        CommandLine merge = cl.getSubCommandLine("merge");
        merge.addOption("--force", null, "Tries to merge the proof bundles even if the files check fails (may rename some files). Only use if you know what you are doing!");
        merge.addOption("--check", "check_arguments", "Performs a check after successful merge. The arguments are passed too check");

        // enable check option forwarding for merge command
        merge.addSubCommand("check");
        CommandLine merge_check = merge.getSubCommandLine("check");
        merge_check.addOption("--settings", null, "Enables check for consistent proof settings");
        merge_check.addOption("--dependency", null, "Enables check for cyclic dependencies");
        merge_check.addOption("--files", null, "Enables check for compatible files");
        merge_check.addOption("--report", "out_path", "Writes the report to a HTML file at the given path");

        // TODO: bundle subcommand
        cl.addSubCommand("bundle");

        return cl;
    }

    public static void main(String[] args) {
        System.out.println("Proof management is running ...");

        try {
            CommandLine cl = setUpCL();
            cl.parse(args);
            if (cl.subCommandUsed("check")) {
                check(cl.getSubCommandLine("check"));
            } else if (cl.subCommandUsed("merge")) {
                merge(cl.getSubCommandLine("merge"));
            } else if (cl.subCommandUsed("bundle")) {
                bundle(cl.getSubCommandLine("bundle"));
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

        Path bundlePath = Paths.get(arguments.get(0));
        ProofBundleHandler pbh = new ProofBundleHandler(bundlePath);

        List<Path> proofFiles = new ArrayList<>();
        try {
            proofFiles.addAll(pbh.getProofFiles());
        } catch (ZipException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }

        // we accumulate results in this variable
        CheckerData globalResult = new CheckerData(true, pbh);
        try {
            // add file tree to result
            globalResult = globalResult.join(new CheckerData(pbh, pbh.getFileTree()));

            // completeness check
            globalResult = globalResult.join(new MissingProofsChecker().check(proofFiles, globalResult));
        } catch (IOException e) {
            e.printStackTrace();
        }

        if (commandLine.isSet("--settings")) {
            CheckerData result = new SettingsChecker().check(proofFiles, globalResult);
            globalResult = globalResult.join(result);
            if (result.isConsistent()) {
                System.out.println("    Consistent! Settings consistent!");
            } else {
                System.out.println("    Inconsistent! Settings do not match!");
            }
        }
        if (commandLine.isSet("--dependency")) {
            CheckerData result = new DependencyChecker().check(proofFiles, globalResult);
            globalResult = globalResult.join(result);
            if (result.isConsistent()) {
                System.out.println("    Consistent! No cycles found!");
            } else {
                System.out.println("    Inconsistent! Cyclic dependency found!");
            }
        }
        // TODO: it is not clear what a file checker could do for only a single bundle ...
        /*
        if (commandLine.isSet("--files")) {
            List<Path> list = new ArrayList<>();
            list.add(bundlePath);
            CheckResult result = new FilesChecker().check(list);
            globalResult = globalResult.join(result);
            if (result.isConsistent()) {
                System.out.println("    Consistent! Files consistent!");
            } else {
                System.out.println("    Inconsistent! Different files found in bundles!");
            }
        }
        */
        pbh.dispose();

        if (commandLine.isSet("--report")) {
            String outFileName = commandLine.getString("--report", "");
            Path output = Paths.get(outFileName).toAbsolutePath();
            Report report = new Report(globalResult);
            report.setOutPath(output);
            try {
                System.out.println(report.printReport());
            } catch (IOException e) {
                e.printStackTrace();
            } catch (URISyntaxException e) {
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
