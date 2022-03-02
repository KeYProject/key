package sourcerer;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.convenience.Format;
import recoder.io.DefaultProjectFileIO;
import recoder.io.DefaultSourceFileRepository;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.kit.Problem;
import recoder.kit.ProblemReport;
import recoder.kit.Transformation;
import recoder.service.ChangeHistoryEvent;
import recoder.service.ChangeHistoryListener;
import recoder.service.ModelUpdateListener;
import recoder.service.TreeChange;
import recoder.util.FileCollector;
import recoder.util.ProgressEvent;
import recoder.util.ProgressListener;

/**
 * Auxiliary class for RECODER applications.
 * 
 * @author AL
 */
public class RecoderProgram {

    /**
     * Simple change history, model update and progress listener, writing out
     * progress messages and change reports.
     */
    public static class ConsoleReports implements ChangeHistoryListener, ModelUpdateListener, ProgressListener {

        private PrintWriter out;

        private int count = 0;

        public ConsoleReports(PrintWriter out) {
            if (out == null) {
                throw new NullPointerException("No output");
            }
            this.out = out;
        }

        public void modelChanged(ChangeHistoryEvent changes) {
            List<TreeChange> news = changes.getChanges();
            for (int i = 0, s = news.size(); i < s; i += 1) {
                ProgramElement pe = news.get(i).getChangeRoot();
                if (pe instanceof CompilationUnit) {
                    count += 1;
                    out.println("[" + count + "] " + ((CompilationUnit) pe).getName());
                    out.flush();
                }
            }
        }

        private long updateBeginTime;

        public void modelUpdating(java.util.EventObject event) {
            out.println("Model Update Starts...");
            out.flush();
            updateBeginTime = System.currentTimeMillis();
        }

        public void modelUpdated(java.util.EventObject event) {
            long updateTime = System.currentTimeMillis() - updateBeginTime;
            out.println("...Model Updated in " + updateTime + "ms");
            out.flush();
        }

        private int oldpercentage = -1;

        private Object oldstate = null;

        private long lastDisplayTime = 0L;

        static final long MIN_DELAY = 200; // ms

        static final int MAX_LINE_WIDTH = 77;

        public void workProgressed(ProgressEvent pe) {
            int max = pe.getWorkToDoCount();
            int val = pe.getWorkDoneCount();
            if (val == max) {
                val = 0;
                oldpercentage = -1;
                oldstate = null;
                StringBuffer output = new StringBuffer("\r100% (done)");
                for (int i = output.length(); i < MAX_LINE_WIDTH; i++) {
                    output.append(' ');
                }
                out.println(output);
                out.flush();
                // no need to reset lastDisplayTime
                return;
            }
            if (val > max) {
                max = val;
            }
            if (System.currentTimeMillis() - lastDisplayTime > MIN_DELAY) {
                int p = 100 * val / max;
                Object state = pe.getState();
                if (p != oldpercentage || state != oldstate) {
                    StringBuffer output = new StringBuffer("\r");
                    if (p < 10) {
                        output.append("  ");
                    } else if (p < 100) {
                        output.append(" ");
                    }
                    output.append(p);
                    output.append('%');
                    if (state != null) {
                        output.append(' ');
                        String msg = state.toString();
                        int msglength = msg.length();
                        int oversize = msglength - (MAX_LINE_WIDTH - 5);
                        if (oversize > 0) {
                            int middle = (msglength - oversize - 3 + 1) / 2;
                            output.append(msg.substring(0, middle));
                            output.append("...");
                            output.append(msg.substring(msglength - middle, msglength));
                        } else {
                            output.append(msg);
                        }
                    }
                    for (int i = output.length(); i < MAX_LINE_WIDTH; i++) {
                        output.append(' ');
                    }
                    out.print(output);
                    out.flush();
                    lastDisplayTime = System.currentTimeMillis();
                    oldpercentage = p;
                    oldstate = state;
                }
            }
        }
    }

    public final static ConsoleReports CONSOLE_OUTPUT = new ConsoleReports(new PrintWriter(System.out));

    private static void warn(String message) {
        System.err.println(message);
    }

    private static void fail(String message) {
        System.err.println(message);
        System.exit(1);
    }

    private static void usage(String progname) {
        fail("Usage: java " + progname + " where admissible arguments are:\n"
                + "  -Q                   suppress progress messages\n"
                + "  <project file>.prj   load properties file to set up system\n"
                + "  <source file>.java   load a single source file to start\n"
                + "  <directory>          load source files recursively from the directory given\n"
                + "  -P                   load source files recursively from the path\n"
                + "  <class name>         load a source or class file with the given logical name\n");
    }

    private static void ensureSystemClassesAreInPath(ServiceConfiguration sc) {
        if (!sc.getProjectSettings().ensureSystemClassesAreInPath()) {
            fail("Problem with system setup: Cannot locate system classes");
        }
    }

    private static boolean isLogicalClassName(String name) {
        if (!Character.isJavaIdentifierStart(name.charAt(0))) {
            return false;
        }
        for (int i = 1, s = name.length(); i < s; i += 1) {
            char x = name.charAt(i);
            if (x == '.') {
                if (name.charAt(i - 1) == '.') {
                    return false;
                }
            } else if (!Character.isJavaIdentifierPart(x)) {
                return false;
            }
        }
        return true;
    }

    private static String[] collectJavaFiles(String dir) {
        FileCollector col = new FileCollector(dir);
        List<String> list = new ArrayList<String>();
        while (col.next(DefaultSourceFileRepository.JAVA_FILENAME_FILTER)) {
            String path;
            try {
                path = col.getFile().getCanonicalPath();
            } catch (IOException ioe) {
                path = col.getFile().getAbsolutePath();
            }
            list.add(path);
        }
        return list.toArray(new String[list.size()]);
    }

    /**
     * Checks the arguments for a single project file, attempts to open the file
     * and reads in all classes defined within.
     * 
     * @param sc
     *            the service configuration to use, usually CrossReference.
     * @param main
     *            the caller object, used for usage instructions.
     * @param args
     *            the command line arguments.
     */
    public static void setup(ServiceConfiguration sc, Class main, String[] args) {
        if (sc == null) {
            throw new IllegalArgumentException("Service configuration required");
        }
        if (main == null) {
            throw new IllegalArgumentException("Main class required");
        }
        if (args == null) {
            throw new IllegalArgumentException("Arguments required");
        }
        if (args.length == 0) {
            usage(main.getName());
        }
        boolean qOptionOccured = false;
        for (int i = args.length - 1; i >= 0; i -= 1) {
            if (args[i].toUpperCase().equals("-Q")) {
                qOptionOccured = true;
                break;
            }
        }
        SourceFileRepository sfr = sc.getSourceFileRepository();
        if (!qOptionOccured) {
            sc.getChangeHistory().addChangeHistoryListener(CONSOLE_OUTPUT);
            sc.getChangeHistory().addModelUpdateListener(CONSOLE_OUTPUT);
            sc.getSourceInfo().addProgressListener(CONSOLE_OUTPUT);
            sfr.addProgressListener(CONSOLE_OUTPUT);
        }
        boolean pOptionOccured = false;
        try {
            ensureSystemClassesAreInPath(sc);
            sc.getProjectSettings().ensureExtensionClassesAreInPath();
            for (int i = 0; i < args.length; i += 1) {
                String a = args[i].toUpperCase();
                if (a.endsWith(".PRJ")) {
                    File projectFile = new File(args[i]);
                    if (!projectFile.isFile()) {
                        warn(args[i] + " is not a file - ignoring");
                    } else {
                        String[] files = new DefaultProjectFileIO(sc, projectFile).load();
                        if (files.length == 1 && files[0].equalsIgnoreCase("all")) {
                            sfr.getAllCompilationUnitsFromPath();
                        } else if (sfr.getCompilationUnitsFromFiles(files).size() < files.length) {
                            warn("Could not load some files from " + args[i] + " - ignoring");
                        }
                        ensureSystemClassesAreInPath(sc); // redo
                    }
                } else if (a.endsWith(".JAVA")) {
                    if (sfr.getCompilationUnitFromFile(args[i]) == null) {
                        warn("Could not load " + args[i] + " - ignoring");
                    }
                } else if (a.equals("-P")) {
                    if (pOptionOccured) {
                        warn("Ignoring redundant -P flag");
                    } else {
                        pOptionOccured = true;
                        // retrieve everything from the search path
                        sfr.getAllCompilationUnitsFromPath();
                    }
                } else if (a.equals("-?") || a.equals("?") || a.equals("-H")) {
                    usage(main.getName());
                } else if (new File(args[i]).isDirectory()) {
                    String[] files = collectJavaFiles(args[i]);
                    if (sfr.getCompilationUnitsFromFiles(files).size() < files.length) {
                        warn("Could not load some files from " + args[i] + " - ignoring");
                    }
                } else if (isLogicalClassName(args[i])) {
                    if (sfr.getCompilationUnit(args[i]) == null) {
                        warn("Could not find class with logical name " + args[i] + " - ignoring argument");
                    }
                } else if (a.endsWith(".JAR")) {
                	sfr.getServiceConfiguration().getProjectSettings().getSearchPathList().add(args[i]);
                } else if (!args[i].startsWith("-")) {
                    warn("Bad argument " + args[i] + " - ignoring");
                }
            }
        } catch (IOException ioe) {
            fail("An IO Exception has occured: " + ioe);
        } catch (ParserException pe) {
            fail("A Parse Error has occured: " + pe);
        }
    }

    /**
     * Calls the proper setup routine, executes the given transformation, and
     * writes back all changed compilation units automatically.
     * 
     * @param transform
     *            the transformation to execute.
     * @param args
     *            the command line arguments, should contain the project file
     *            name as only argument.
     */
    public static void execute(Transformation transform, String[] args) {
        ServiceConfiguration sc = transform.getServiceConfiguration();
        setup(sc, transform.getClass(), args);
        ProblemReport report = transform.execute();
        if (report instanceof Problem) {
            warn(report.toString());
        } else {
            System.out.println("Transformation succeeded - writing results");
            SourceFileRepository sfr = sc.getSourceFileRepository();
            List<CompilationUnit> units = sfr.getCompilationUnits();
            for (int i = 0; i < units.size(); i += 1) {
                CompilationUnit cu = units.get(i);
                if (!sfr.isUpToDate(cu)) {
                    System.out.println(Format.toString("%u [%f]", cu));
                    try {
                        sc.getSourceFileRepository().print(cu);
                    } catch (IOException ioe) {
                        warn("An IO Exception has occured: " + ioe);
                    }
                }
            }
        }
    }

}
