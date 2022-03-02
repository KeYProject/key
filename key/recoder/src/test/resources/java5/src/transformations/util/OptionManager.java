// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

import java.io.PrintStream;
import java.util.Enumeration;
import java.util.Vector;

/**
 * provides methods for dealing with command line arguments.
 * 
 * @author RN
 */
public class OptionManager {

    public static final int SIMPLE = 0;

    public static final int SWITCH = 1;

    public static final int BOOL = 2;

    public static final int NUM = 3;

    public static final int STRING = 4;

    private static final String[] optVals = { "", "on|off", "true|false", "<n>", "<s>", };

    public static final Boolean TRUE = Boolean.TRUE;

    public static final Boolean FALSE = Boolean.FALSE;

    public static final Boolean ON = TRUE;

    public static final Boolean OFF = FALSE;

    public static final int ONE = 1;

    public static final int ZERO_OR_ONE = 2;

    public static final int ONE_OR_MORE = 4;

    public static final int ZERO_OR_MORE = 8;

    private static final int SINGLE = ONE | ZERO_OR_ONE;

    private static final int MULTI = ZERO_OR_MORE | ONE_OR_MORE;

    private static final int MANDATORY = ONE | ONE_OR_MORE;

    /** describes a single command line option. */
    private class OptionDescription {
        int type;

        int multiplicity;

        String shortOpt;

        String longOpt;

        String description;

        Vector values = new Vector();
    }

    /** the registered possible options */
    Vector options = new Vector();

    /** maps strings to their according option objects */
    MutableMap str2opt = new NaturalHashTable();

    /** the mandatory options */
    Vector mandatories = new Vector();

    /** adds the given option to the registered ones */
    public void addOption(int type, String shortOpt, String longOpt, String description) {
        addOption(type, ZERO_OR_ONE, shortOpt, longOpt, description);
    }

    /** adds the given option to the registered ones */
    public void addOption(int type, int multiplicity, String shortOpt, String longOpt, String description) {
        Debug.assertBoolean(SIMPLE <= type && type <= STRING, "Illegal option type");
        Debug.assertBoolean(ONE <= multiplicity && multiplicity <= ZERO_OR_MORE, "Illegal multiplicity specification");
        Debug.assertNonnull(shortOpt, "No short id specified");
        Debug.assertNonnull(longOpt, "No long id specified");
        Debug.assertNonnull(description, "No description specified");

        OptionDescription descr = new OptionDescription();
        descr.type = type;
        descr.multiplicity = multiplicity;
        descr.shortOpt = shortOpt;
        descr.longOpt = longOpt;
        descr.description = description;
        options.addElement(descr);
        str2opt.put("-" + shortOpt, descr);
        str2opt.put("--" + longOpt, descr);
        if ((multiplicity & MANDATORY) != 0) {
            mandatories.addElement(descr);
        }
    }

    int getOptionCount() {
        return options.size();
    }

    /** parses the argument at the given position */
    int parseArg(String[] args, int offset) throws UnknownOptionException, OptionMultiplicityException,
            IllegalOptionValueException, MissingOptionValueException {
        String opt = args[offset];
        OptionDescription descr = (OptionDescription) str2opt.get(opt);
        if (descr == null) {
            throw new UnknownOptionException(args[offset]);
        }
        // first check for multiplicity constraints
        if ((descr.multiplicity & SINGLE) != 0 && descr.values.size() > 0) {
            throw new OptionMultiplicityException(opt);
        }
        offset++;
        // now compute the value
        String sval = null;
        if (descr.type != SIMPLE) {
            if (offset == args.length) {
                throw new MissingOptionValueException(opt);
            }
            sval = args[offset++];
        }
        Object optval = null;
        switch (descr.type) {
        case SIMPLE:
            optval = TRUE;
            break;
        case SWITCH:
            if ("on".equals(sval)) {
                optval = ON;
            } else if ("off".equals(sval)) {
                optval = OFF;
            } else {
                throw new IllegalOptionValueException(opt, sval);
            }
            break;
        case BOOL:
            if ("true".equals(sval)) {
                optval = TRUE;
            } else if ("false".equals(sval)) {
                optval = FALSE;
            } else {
                throw new IllegalOptionValueException(opt, sval);
            }
            break;
        case NUM:
            try {
                optval = new Integer(sval);
            } catch (NumberFormatException nfe) {
                throw new IllegalOptionValueException(opt, sval);
            }
            break;
        case STRING:
            optval = sval;
            break;
        }
        Debug.assertNonnull(optval);
        descr.values.addElement(optval);
        return offset;
    }

    /**
     * parses all the options within the given arguments and return the
     * remaining unparsed arguments.
     */
    public String[] parseArgs(String[] args) throws UnknownOptionException, OptionMultiplicityException,
            IllegalOptionValueException, MissingOptionValueException, MissingArgumentException {
        int offset = 0;
        while (offset < args.length && args[offset].startsWith("-")) {
            offset = parseArg(args, offset);
        }
        // check if all mandatory arguments have been set
        for (Enumeration mand = mandatories.elements(); mand.hasMoreElements();) {
            OptionDescription descr = (OptionDescription) mand.nextElement();
            if (descr.values.size() == 0) {
                throw new MissingArgumentException(descr.shortOpt);
            }
        }
        String[] result = new String[args.length - offset];
        System.arraycopy(args, offset, result, 0, result.length);
        return result;
    }

    protected void printArg(PrintStream out, OptionDescription descr) {
        String baseinfo = ("-" + descr.shortOpt + " " + optVals[descr.type]).trim();
        String arginfo = "";
        switch (descr.multiplicity) {
        case ONE:
            arginfo = " " + baseinfo;
            break;
        case ZERO_OR_ONE:
            arginfo = " [" + baseinfo + "]";
            break;
        case ONE_OR_MORE:
            arginfo = " " + baseinfo + " [" + baseinfo + " ... " + baseinfo + "]";
            break;
        case ZERO_OR_MORE:
            arginfo = " [" + baseinfo + " ... " + baseinfo + "]";
            break;
        }
        out.print(arginfo);
    }

    private final static String empty = "                                     ";

    protected void printInfo(PrintStream out, OptionDescription descr, int sl, int ll, int vl) {
        String ss = (descr.shortOpt + empty).substring(0, sl);
        String ls = (descr.longOpt + empty).substring(0, ll);
        String vs = (optVals[descr.type] + empty).substring(0, vl);
        out.println("  -" + ss + " " + vs + " | --" + ls + " " + vs + " : " + descr.description);
    }

    /** prints usage information to the given output stream */
    public void showUsage(PrintStream out, String programName, String params, boolean detailed) {
        out.print("usage: " + programName);
        int sl = 0;
        int ll = 0;
        int vl = 0;
        for (int i = 0; i < options.size(); i++) {
            OptionDescription descr = (OptionDescription) options.elementAt(i);
            sl = Math.max(sl, descr.shortOpt.length());
            ll = Math.max(ll, descr.longOpt.length());
            vl = Math.max(vl, optVals[descr.type].length());
            printArg(out, descr);
        }
        out.println(" " + params);
        if (detailed) {
            for (int i = 0; i < options.size(); i++) {
                printInfo(out, (OptionDescription) options.elementAt(i), sl, ll, vl);
            }
        }
    }

    /** prints usage information to the standard output stream */
    public void showUsage(String programName, String params, boolean detailed) {
        showUsage(System.out, programName, params, detailed);
    }

    /** returns the values set for the given value */
    public Vector getValues(String opt) {
        OptionDescription descr = (OptionDescription) str2opt.get("-" + opt);
        if (descr == null) {
            return null;
        }
        return descr.values;
    }

    /** retrieves the value set for the given option (assumes single value) */
    public Object getValue(String opt) {
        Vector vals = getValues(opt);
        if (vals != null && vals.size() > 0) {
            return vals.elementAt(0);
        } else {
            return null;
        }
    }

    /** returns true if the given flag option is set */
    public boolean isSet(String opt) {
        return getValue(opt) == TRUE;
    }

    /** returns the boolean interpretation of the specified value */
    public boolean getBooleanVal(String opt) {
        return getBooleanVal(opt, false);
    }

    /** returns the boolean interpretation of the specified value */
    public boolean getBooleanVal(String opt, boolean defaultVal) {
        Object v = getValue(opt);
        if (v == null) {
            return defaultVal;
        } else {
            return v == TRUE;
        }
    }

    /** returns the integer interpretation of the specified value */
    public int getIntVal(String opt) {
        return getIntVal(opt, 0);
    }

    /** returns the integer interpretation of the specified value */
    public int getIntVal(String opt, int defaultVal) {
        Object v = getValue(opt);
        if (v == TRUE) {
            return 1;
        } else if (v == FALSE) {
            return 0;
        } else {
            try {
                Integer i = (Integer) v; // may raise ClassCastException
                return i.intValue(); // may raise NullPointerException
            } catch (Exception e) {
                // nothing to de here
            }
        }
        return defaultVal;
    }

    /** returns the string interpretation of the specified value */
    public String getStringVal(String opt) {
        return getStringVal(opt, null);
    }

    /** returns the string interpretation of the specified value */
    public String getStringVal(String opt, String defaultVal) {
        String result = (String) getValue(opt);
        if (result == null) {
            return defaultVal;
        } else {
            return result;
        }
    }

}