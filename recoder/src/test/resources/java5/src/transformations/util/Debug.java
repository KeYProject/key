// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Properties;

/**
 * Routines to debug.
 * 
 * @author UA
 * @author AL
 */
public class Debug {

    /**
     * Information level. Lower levels are higher.
     */
    protected static int level = 1;

    /**
     * The print writer output stream.
     */
    // protected static PrintWriter output = new PrintWriter(System.err);
    protected static PrintStream output = System.err;

    /**
     * Strings that are regarded as having a somewhat negative touch. Options
     * with these values (or uppercase versions thereof) are considered unset.
     */
    protected final static String[] NEGATIVE_VALUES = new String[] { "", "0", "false", "off", "no", "none" };

    protected final static String DEBUGGING_OPTION_FILE = "debug.properties";

    /**
     * Debugging print functions. Maintains an option table to steer debug
     * printout.
     */
    private static Properties debuggingOptions = null;

    final static String ESC_PREFIX = "\033[3;31m";

    final static String ESC_SUFFIX = "\033[0m";

    static String ERROR_MESSAGE = "Error: ";

    static String RESTRICTION_MESSAGE = "Restriction: ";

    static String INFO_MESSAGE = "Info: ";

    static String ASSERTION_MESSAGE = "Assertion failed: ";

    protected static Properties getDebuggingOptions() {
        if (debuggingOptions == null) {
            debuggingOptions = new Properties();
            try {
                debuggingOptions.load(new FileInputStream(DEBUGGING_OPTION_FILE));
            } catch (IOException ioe) {
                // error("Could not find option file " + DEBUGGING_OPTION_FILE);
            }
        }
        return debuggingOptions;
    }

    /**
     * Finds out whether the properties contain a key with the given name and
     * whether it is set to a positive value. Positives values are everything
     * but "", "0", "false", "off", "no", "none".
     */
    protected static boolean isSet(Properties prop, String key) {
        String value = prop.getProperty(key);
        if (value == null) {
            return false;
        }
        for (int i = 0; i < NEGATIVE_VALUES.length; i++) {
            if (NEGATIVE_VALUES[i].equalsIgnoreCase(value)) {
                return false;
            }
        }
        return true;
    }

    public static boolean isSet(String key) {
        return isSet(getDebuggingOptions(), key);
    }

    /**
     * Gets current debug output detail level.
     */
    public static int getLevel() {
        return level;
    }

    /**
     * Sets current debug output detail level.
     */
    public static void setLevel(int level) {
        Debug.level = level;
    }

    public static void setOutput(PrintStream s) {
        if (s == null) {
            throw new NullPointerException();
        }
        output = s;
    }

    /**
     * Print out a string if it the option is set. At first call, read the
     * properties from file .recoderrc.
     */
    public static void println(String option, String printoutString) {
        if (isSet(getDebuggingOptions(), option)) {
            System.out.println(printoutString);
        }
    }

    /**
     * Print out a string if it the option is set. print the option string also.
     */
    public static void printlno(String option, String printoutString) {
        if (isSet(getDebuggingOptions(), option)) {
            System.out.println("Option " + option + ":" + printoutString);
        }
    }

    /**
     * Sets a property in the debugging option table.
     */
    public static void setOption(String key, String value) {
        getDebuggingOptions().put(key, value);
    }

    /**
     * Prints an error (always).
     */
    public static void error(String error) {
        if (isSet("terminal.escapes")) {
            output.println(ESC_PREFIX + ERROR_MESSAGE + ESC_SUFFIX + error);
        } else {
            output.println(ERROR_MESSAGE + error);
        }
    }

    /**
     * Prints an implementation restriction (always).
     */
    public static void restriction(String restriction) {
        output.println(RESTRICTION_MESSAGE + restriction);
    }

    /**
     * Prints a message (always).
     */
    public static void log(String info) {
        output.println(info);
    }

    /**
     * Prints an information (always).
     */
    public static void info(String info) {
        output.println(INFO_MESSAGE + info);
    }

    /**
     * Prints an information, depending on level.
     */
    public static void info(int level, String info) {
        if (Debug.level >= level) {
            output.println(INFO_MESSAGE + info);
        }
    }

    /**
     * Assertion method for general conditions.
     * 
     * @param expression
     *            predicate that must hold.
     * @exception IllegalStateException
     *                if the expression evaluates to false.
     */
    public final static void assertBoolean(boolean expression) {
        if (!expression) {
            throw new IllegalStateException(ASSERTION_MESSAGE + "(general condition)");
        }
    }

    /**
     * Assertion method for general conditions.
     * 
     * @param expression
     *            predicate that must hold.
     * @param message
     *            detail message.
     * @exception IllegalStateException
     *                if the expression evaluates to false.
     */
    public final static void assertBoolean(boolean expression, String message) {
        if (!expression) {
            throw new IllegalStateException(ASSERTION_MESSAGE + message);
        }
    }

    /**
     * Special assertion method to test for invalid objects.
     * 
     * @param nonnull
     *            object that may not be null.
     * @exception NullPointerException
     *                if the object is null.
     */
    public final static void assertNonnull(Object nonnull) {
        if (nonnull == null) {
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object)" + "\n");
        }
    }

    /**
     * Special assertion method to test for invalid objects.
     * 
     * @param nonnull1
     *            object that may not be null.
     * @param nonnull2
     *            object that may not be null.
     * @exception NullPointerException
     *                if the object is null.
     */
    public final static void assertNonnull(Object nonnull1, Object nonnull2) {
        if (nonnull1 == null) {
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 1)" + "\n");
        }
        if (nonnull2 == null) {
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 2)" + "\n");
        }
    }

    /**
     * Special assertion method to test for invalid objects.
     * 
     * @param nonnull1
     *            object that may not be null.
     * @param nonnull2
     *            object that may not be null.
     * @param nonnull3
     *            object that may not be null.
     * @exception NullPointerException
     *                if the object is null.
     */
    public final static void assertNonnull(Object nonnull1, Object nonnull2, Object nonnull3) {
        if (nonnull1 == null) {
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 1)" + "\n");
        }
        if (nonnull2 == null) {
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 2)" + "\n");
        }
        if (nonnull3 == null) {
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 3)" + "\n");
        }
    }

    /**
     * Special assertion method to test for invalid objects.
     * 
     * @param nonnull1
     *            object that may not be null.
     * @param nonnull2
     *            object that may not be null.
     * @param nonnull3
     *            object that may not be null.
     * @param nonnull4
     *            object that may not be null.
     * @exception NullPointerException
     *                if the object is null.
     */
    public final static void assertNonnull(Object nonnull1, Object nonnull2, Object nonnull3, Object nonnull4) {
        if (nonnull1 == null) {
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 1)" + "\n");
        }
        if (nonnull2 == null) {
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 2)" + "\n");
        }
        if (nonnull3 == null) {
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 3)" + "\n");
        }
        if (nonnull4 == null) {
            throw new NullPointerException(ASSERTION_MESSAGE + "(Null object 4)" + "\n");
        }
    }

    /**
     * Special assertion method to test for invalid objects.
     * 
     * @param nonnull
     *            object that may not be null.
     * @param message
     *            detail message.
     * @exception NullPointerException
     *                if the object is null.
     */
    public final static void assertNonnull(Object nonnull, String message) {
        if (nonnull == null) {
            throw new NullPointerException(ASSERTION_MESSAGE + message);
        }
    }

    /**
     * Receives a string with a stack trace for the caller of this method. The
     * implementation assumes that the output format of
     * Throwable.printStackTrace does not change in future versions of the JDK.
     * The resulting string contains no exception name and does not end with a
     * linefeed.
     */
    public final static String makeStackTrace() {
        StringWriter buf = new StringWriter();
        try {
            throw new RuntimeException();
        } catch (RuntimeException e) {
            e.printStackTrace(new PrintWriter(buf));
        }
        buf.flush();
        String str = buf.toString();
        int begin = str.indexOf('\n', str.indexOf('\n') + 1) + 1;
        return str.substring(begin, str.lastIndexOf('\n'));
    }

    /**
     * Returns the amount of memory used by the virtual machine. Generational
     * garbage collectors might obscure the result; therefore, the garbage
     * collector is run until only minor changes are observed.
     */
    public final static long getUsedMemory() {
        Runtime run = Runtime.getRuntime();
        long totalMem = run.totalMemory();
        long freeMem = run.freeMemory();
        long oldFreeMem;
        do {
            run.gc();
            oldFreeMem = freeMem;
            freeMem = run.freeMemory();
        } while (freeMem > oldFreeMem + 256); // allow addition of 256 bytes
        return totalMem - freeMem;
    }
}