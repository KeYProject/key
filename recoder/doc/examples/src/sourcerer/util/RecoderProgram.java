package sourcerer.util;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
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
import recoder.service.TreeChange;
import recoder.util.FileCollector;

/**
   Auxiliary class for COMPOST applications.
   @author AL
 */
public class RecoderProgram {

    /**
       Simple change history listener, writing out the names of compilation 
       units that have arrived.
     */
    static class ImportReport implements ChangeHistoryListener {
	
	private int count = 0;
	private PrintWriter out;
	
	public ImportReport(PrintWriter out) {
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
		    out.println("[" + count + "] " +
				((CompilationUnit)pe).getName());
		    out.flush();
		}
	    }
	}
    }

    public final static ChangeHistoryListener CONSOLE_OUTPUT = 
	new ImportReport(new PrintWriter(System.out));
    
    private static void warn(String message) {
	System.err.println(message);
    }
    
    private static void fail(String message) {
	System.err.println(message);
	System.exit(1);
    }

    private static void usage(String progname) {
	fail("Usage: java " + progname +
	     " where admissible arguments are:\n" +
	     "  <project file>.prj   load properties file to set up system\n" +
	     "  <source file>.java   load a single source file to start\n" +
	     "  <directory>          load source files recursively from the directory given\n" +
	     "  -P                   load source files recursively from the path\n" +
	     "  <class name>         load a source or class file with the given logical name\n");
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
    
    /**
       Checks the arguments for a single project file, attempts to open
       the file and reads in all classes defined within.
       @param sc the service configuration to use, usually CrossReference.
       @param main the caller object, used for usage instructions.
       @param args the command line arguments.
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
	sc.getChangeHistory().addChangeHistoryListener(CONSOLE_OUTPUT);
	SourceFileRepository sfr = sc.getSourceFileRepository();

	boolean pOptionOccured = false;
	try {
	    ensureSystemClassesAreInPath(sc);
	    for (int i = 0; i < args.length; i += 1) {
		String a = args[i].toUpperCase();
		if (a.endsWith(".PRJ")) {
		    File projectFile = new File(args[i]);
		    if (!projectFile.isFile()) {
			warn(args[i] + " is not a file - ignoring");
		    } else {
			new DefaultProjectFileIO(sc, projectFile).load();
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
		    FileCollector col = new FileCollector(args[i]);		
		    while (col.next(DefaultSourceFileRepository.JAVA_FILENAME_FILTER)) {
			String filename = col.getFile().getAbsolutePath();
			if (sfr.getCompilationUnitFromFile(filename) == null) {
			    warn("Warning - could not load " + filename);
			}
		    }
		} else if (isLogicalClassName(args[i])) {
		    if (sfr.getCompilationUnit(args[i]) == null) {
			warn("Could not find class with logical name " + args[i] + " - ignoring argument");
		    }
		} else {
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
       Calls the proper setup routine, executes the given transformation,
       and writes back all changed compilation units automatically.
       @param transform the transformation to execute.
       @param args the command line arguments, should contain the project file
       name as only argument.
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
