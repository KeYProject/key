/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.util;

import java.lang.reflect.Field;
import java.util.HashMap;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.kit.pattern.FactoryMethod;

/**
 * This class can be used either as a template or as a base class for building RECODER command line
 * applications.
 * <p>
 * It allows to write transformation, refactoring, and composition programs. It provides command
 * argument processing.
 * <p>
 * The class is a template class with hook methods:
 * <ul>
 * <li>The actual application code must be contained in an abstract run method which must be filled
 * by a subclass. Processing starts with a predefined start method which calls the run method after
 * argument processing.</li>
 * <li>To adapt the option processing, the methods to register options are provided. The options are
 * registered two-fold.
 * <ul>
 * <li>First of all, attributes of the subclass are set by supplying their attribute name.</li>
 * <li>Then, the option is registered with the OptionManager.</li>
 * </ul>
 * </li>
 * </ul>
 *
 * @author RN
 */
public abstract class CommandLineProgram {
    private static final Logger LOGGER = LoggerFactory.getLogger(FactoryMethod.class);

    // some variables that may be used as default values by derived classes

    public static final Boolean TRUE = OptionManager.TRUE;

    public static final Boolean FALSE = OptionManager.FALSE;

    public static final Boolean ON = OptionManager.ON;

    public static final Boolean OFF = OptionManager.OFF;

    public static final int ONE = OptionManager.ONE;

    public static final int ZERO_OR_ONE = OptionManager.ZERO_OR_ONE;

    public static final int ONE_OR_MORE = OptionManager.ONE_OR_MORE;

    public static final int ZERO_OR_MORE = OptionManager.ZERO_OR_MORE;
    // the following methods have to be redefined in derived classes
    private final OptionManager om = new OptionManager();
    private final java.util.Map<String, Field> vars = new HashMap<>();
    // by default the command line program provides a simple help facility
    public boolean showHelp;

    protected abstract String getArgsDescription();

    protected abstract void run(String[] args) throws Exception;

    /**
     * The following registration method for options may be extended - but don't forget to call this
     * one.
     */

    protected void registerOptions() {
        registerSimpleOpt("showHelp", "h", "help", "display help information");
    }

    // the following methods are used to register options

    /**
     * Creates a new program instance. First, register options, parse arguments, set variables. If
     * nothing went wrong, call the run method of the subclass.
     */
    protected final void start(String[] args) {
        try {
            registerOptions();
            String[] remainingArgs = parseArgs(args);
            setVariables();
            if (showHelp) {
                usage(true, 0);
            }
            run(remainingArgs);
        } catch (OptionException oe) {
            handleOptionException(oe);
        } catch (Exception e) {
            LOGGER.warn("Failed", e);
            System.exit(1);
        }
    }

    protected void handleOptionException(OptionException oe) {
        try {
            setVariables();
        } catch (Exception e) {
        }
        if (showHelp) {
            usage(true, 0);
        } else {
            LOGGER.warn("Error", oe);
            usage(false, 1);
        }
    }

    protected final void registerSimpleOpt(String varName, String shortOpt, String longOpt,
            String descr) {
        registerSimpleOpt(varName, shortOpt, longOpt, descr, ZERO_OR_ONE);
    }

    protected final void registerSimpleOpt(String varName, String shortOpt, String longOpt,
            String descr, int multiplicity) {
        registerVar(varName, shortOpt, Boolean.FALSE);
        om.addOption(OptionManager.SIMPLE, multiplicity, shortOpt, longOpt, descr);
    }

    protected final void registerSwitchOpt(String varName, String shortOpt, String longOpt,
            String descr, boolean defaultVal) {
        registerSwitchOpt(varName, shortOpt, longOpt, descr, ZERO_OR_ONE, defaultVal);
    }

    protected final void registerSwitchOpt(String varName, String shortOpt, String longOpt,
            String descr, int multiplicity, boolean defaultVal) {
        registerVar(varName, shortOpt, defaultVal);
        om.addOption(OptionManager.SWITCH, multiplicity, shortOpt, longOpt, descr);
    }

    protected final void registerBooleanOpt(String varName, String shortOpt, String longOpt,
            String descr, boolean defaultVal) {
        registerBooleanOpt(varName, shortOpt, longOpt, descr, ZERO_OR_ONE, defaultVal);
    }

    protected final void registerBooleanOpt(String varName, String shortOpt, String longOpt,
            String descr, int multiplicity, boolean defaultVal) {
        registerVar(varName, shortOpt, defaultVal);
        om.addOption(OptionManager.BOOL, multiplicity, shortOpt, longOpt, descr);
    }

    protected final void registerNumberOpt(String varName, String shortOpt, String longOpt,
            String descr, int defaultVal) {
        registerNumberOpt(varName, shortOpt, longOpt, descr, ZERO_OR_ONE, defaultVal);
    }

    protected final void registerNumberOpt(String varName, String shortOpt, String longOpt,
            String descr, int multiplicity, int defaultVal) {
        registerVar(varName, shortOpt, defaultVal);
        om.addOption(OptionManager.NUM, multiplicity, shortOpt, longOpt, descr);
    }

    protected final void registerStringOpt(String varName, String shortOpt, String longOpt,
            String descr, String defaultVal) {
        registerStringOpt(varName, shortOpt, longOpt, descr, ZERO_OR_ONE, defaultVal);
    }

    protected final void registerStringOpt(String varName, String shortOpt, String longOpt,
            String descr, int multiplicity, String defaultVal) {
        registerVar(varName, shortOpt, defaultVal);
        om.addOption(OptionManager.STRING, multiplicity, shortOpt, longOpt, descr);
    }

    public void usage(boolean detailed, int exitcode) {
        om.showUsage("java " + getClass().getName(), getArgsDescription(), detailed);
        if (exitcode > -1) {
            System.exit(exitcode);
        }
    }

    private String[] parseArgs(String[] args) throws Exception {
        return om.parseArgs(args);
    }

    private void setVariables() throws Exception {
        for (String s : vars.keySet()) {
            Field f = vars.get(s);
            Object val = om.getValue(s);
            if (val != null) {
                f.set(this, val);
            }
        }
    }

    private void registerVar(String varName, String optStr, Object defVal) {
        try {
            Field var = getClass().getField(varName);
            var.set(this, defVal);
            vars.put(optStr, var);
        } catch (Exception e) {
            throw new RuntimeException("Internal error: " + e);
        }
    }

}
