/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.io;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.io.File;
import java.io.FileFilter;
import java.util.*;

import recoder.AbstractService;
import recoder.ServiceConfiguration;
import recoder.parser.JavaCCParser;
import recoder.service.DefaultErrorHandler;
import recoder.service.ErrorHandler;
import recoder.util.FileUtils;

/**
 * The project settings object manages global properties such as search and output paths, and
 * options for the pretty printer and can save and load a textual representation of these
 * informations.
 *
 * @author RN
 * @author AL
 * @author UH (extension class identification)
 */
public class ProjectSettings extends AbstractService implements PropertyNames {

    private static final FileFilter jarFilter = pathname -> pathname.getPath().endsWith(".jar");
    /**
     * The default properties.
     */
    private final Properties defaults;
    /**
     * The current properties.
     */
    private final Properties properties;
    /**
     * Auxiliary event propagation manager.
     */
    private final PropertyChangeSupport changes = new PropertyChangeSupport(this);
    /**
     * The current search path list.
     */
    private PathList searchPathList;
    /**
     * The error handler.
     */
    private ErrorHandler errorHandler;

    /**
     * Creates a new project settings object for the given service configuration.
     */
    public ProjectSettings(ServiceConfiguration config) {
        super(config);
        defaults = new Properties();
        properties = new Properties(defaults);

        String classpath = getSystemProperty(INPUT_PATH);
        if (classpath == null) {
            classpath = getSystemProperty("java.class.path");
            if (classpath == null) {
                classpath = "";
            } else {
                classpath = normalizeSearchPath(classpath);
            }
        } else {
            classpath = normalizeSearchPath(classpath);
            properties.put(INPUT_PATH, classpath);
        }
        defaults.put(INPUT_PATH, classpath);

        String defaultPath = getSystemProperty("user.dir");
        if (defaultPath == null) {
            defaultPath = ".";
        }
        setDefault(OUTPUT_PATH, defaultPath);
        setDefault(CLASS_SEARCH_MODE, "sc");
        setDefault(ERROR_THRESHOLD, "20");
        setDefault(JDK1_4, "true");
        setDefault(JAVA_5, "true");
        setDefault(ADD_NEWLINE_AT_END_OF_FILE, "true");
        setDefault(INDENTATION_AMOUNT, "4");
        setDefault(OVERWRITE_PARSE_POSITIONS, "false");
        setDefault("wrappingThreshold", "78");
        setDefault(OVERWRITE_INDENTATION, "false");
        setDefault(GLUE_STATEMENT_BLOCKS, "true");
        setDefault(GLUE_SEQUENTIAL_BRANCHES, "true");
        setDefault(GLUE_CONTROL_EXPRESSIONS, "false");
        setDefault(GLUE_PARAMETER_LISTS, "true");
        setDefault(GLUE_PARAMETERS, "false");
        setDefault(GLUE_PARAMETER_PARENTHESES, "true");
        setDefault(GLUE_EXPRESSION_PARENTHESES, "true");
        setDefault(GLUE_INITIALIZER_PARENTHESES, "false");
        setDefault(GLUE_INFIX_OPERATORS, "false");
        setDefault(GLUE_UNARY_OPERATORS, "true");
        setDefault(GLUE_MEMBERS, "false");
        setDefault(GLUE_LABELS, "false");
        setDefault(ALIGN_LABELS, "true");
        setDefault(GLUE_DECLARATION_APPENDICES, "false");
        searchPathList = new PathList(classpath);
    }

    private String getSystemProperty(String propertyName) {
        try {
            return System.getProperty(propertyName);
        } catch (RuntimeException e) {
            return null;
        }
    }

    // checks for system properties first, then uses hard-coded default value
    private void setDefault(String propertyName, String defaultValue) {
        String v = getSystemProperty(propertyName);
        if (v == null) {
            v = defaultValue;
        } else {
            properties.put(propertyName, v);
        }
        defaults.put(propertyName, v);
    }

    public final boolean java5Allowed() {
        return Boolean.valueOf(properties.getProperty(JAVA_5));
    }

    /**
     * Defines a property with the given name and value and informs all registered listeners. The
     * method will automatically remove all segments from the search path that do not exist.
     *
     * @param key the name of the property to set.
     * @param value the value of the property to set.
     * @return the old value associated with the key, or <CODE>null</CODE> if this property has not
     *         been set.
     */
    public String setProperty(String key, String value) {
        String oldValue = properties.getProperty(key);
        if (!Objects.equals(oldValue, value)) {
            if (INPUT_PATH.equals(key)) {
                value = normalizeSearchPath(value);
                searchPathList = new PathList(value);
            } else if (ERROR_THRESHOLD.equals(key)) {
                if (errorHandler != null) {
                    try {
                        errorHandler.setErrorThreshold(Integer.parseInt(value));
                    } catch (NumberFormatException e) {
                        errorHandler.reportError(e);
                        return oldValue;
                    }
                }
            } else if (TABSIZE.equals(key)) {
                try {
                    JavaCCParser.setTabSize(Integer.parseInt(value));
                } catch (NumberFormatException e) {
                    errorHandler.reportError(e);
                    return oldValue;
                }
            }
            properties.put(key, value);
            changes.firePropertyChange(key, oldValue, value);
        }
        return oldValue;
    }

    // initialize at startup; also set as current property

    /**
     * Returns the property with the given name.
     *
     * @param key the name of the property to look for.
     * @return the property associated with the given key.
     */
    public String getProperty(String key) {
        return properties.getProperty(key);
    }

    /**
     * Returns the default property with the given name.
     *
     * @param key the name of the default property to look for.
     * @return the property associated with the given key.
     */
    public String getDefaultProperty(String key) {
        return defaults.getProperty(key);
    }

    /**
     * Returns a copy of the currently valid properties.
     *
     * @return a copy of the currently valid properties.
     */
    public Properties getProperties() {
        return (Properties) properties.clone();
    }

    /**
     * Gets the current input path, removes all paths that do not exist or are duplicated, and
     * writes back the property.
     */
    private String normalizeSearchPath(String pathlist) {
        if (pathlist == null) {
            return null;
        }
        Set<String> alreadyExisting = new HashSet<>();
        StringBuilder newpathlist = new StringBuilder();
        pathlist = pathlist.replace('/', File.separatorChar);
        pathlist = pathlist.replace('\\', File.separatorChar);
        StringTokenizer paths = new StringTokenizer(pathlist, File.pathSeparator);
        boolean firstToken = true;
        while (paths.hasMoreTokens()) {
            String singlePath = paths.nextToken();
            if (!alreadyExisting.contains(singlePath) && new File(singlePath).exists()) {
                if (!firstToken) {
                    newpathlist.append(File.pathSeparator);
                }
                newpathlist.append(singlePath);
                alreadyExisting.add(singlePath);
                firstToken = false;
            }
        }
        pathlist = newpathlist.toString();
        return pathlist;
    }

    /**
     * Ensures that the class file repository can find "java.lang.Object" by adding the proper path
     * to the search path list. This method must be called explicitly after creation of a service
     * configuration.
     *
     * @return <CODE>true</CODE>, if the class file repository knows how to find "Object",
     *         <CODE>false</CODE> otherwise.
     */
    public boolean ensureSystemClassesAreInPath() {
        ClassFileRepository cfr = serviceConfiguration.getClassFileRepository();
        if (cfr.findClassFile("java.lang.Object") != null) {
            return true;
        }
        File archive = FileUtils.getPathOfSystemClasses();
        if (archive == null) {
            archive = new File(".");
        }
        String classes = archive.getPath();
        String oldpath = getProperty(INPUT_PATH);
        if (oldpath.length() == 0) {
            oldpath = ".";
        }
        setProperty(INPUT_PATH, oldpath + File.pathSeparator + classes);
        return cfr.findClassFile("java.lang.Object") != null;
    }

    /**
     * Ensures that the class file repository can find ext classes from the magic directory by
     * adding the proper path to the search path list. This method must be called explicitly after
     * creation of a service configuration.
     *
     * @since 0.72
     */
    public void ensureExtensionClassesAreInPath() {
        File extDir = FileUtils.getPathOfExtensionClassesDir();
        if (extDir == null) {
            return;
        }
        String oldpath = getProperty(INPUT_PATH);
        String extPath = extDir.getPath();
        if (oldpath.contains(extPath)) {
            return;
        }

        // add all the jars from extDir in the path
        StringBuilder additions = null;
        File[] jars = extDir.listFiles(ProjectSettings.jarFilter);
        if (jars.length > 0) {
            additions = new StringBuilder();
            for (File jar : jars) {
                additions.append(File.pathSeparator + jar.getPath());
            }
        }
        setProperty(INPUT_PATH, oldpath + File.pathSeparator + additions);
    }

    /**
     * Registers a property change listener.
     *
     * @param l the listener to register.
     */
    public void addPropertyChangeListener(PropertyChangeListener l) {
        changes.addPropertyChangeListener(l);
    }

    /**
     * Deregisters a property change listener.
     *
     * @param l the listener to deregister.
     */
    public void removePropertyChangeListener(PropertyChangeListener l) {
        changes.removePropertyChangeListener(l);
    }

    /**
     * Returns the current shared search path list.
     *
     * @return the current search path list.
     */
    public PathList getSearchPathList() {
        return searchPathList;
    }

    /**
     * Returns the current error handler. If no error handler is set, a
     * {@link recoder.service.DefaultErrorHandler}will be constructed.
     *
     * @return the current error handler.
     */
    public ErrorHandler getErrorHandler() {
        if (errorHandler == null) {
            setErrorHandler(null);
        }
        return errorHandler;
    }

    /**
     * Sets the current error handler and registers it as a change update listener.
     *
     * @param handler the new error handler.
     */
    public void setErrorHandler(ErrorHandler handler) {
        if (handler == null) {
            handler = new DefaultErrorHandler(Integer.parseInt(getProperty(ERROR_THRESHOLD)));
        }
        if (handler != errorHandler) {
            if (errorHandler != null) {
                serviceConfiguration.getChangeHistory().removeModelUpdateListener(handler);
            }
            errorHandler = handler;
            serviceConfiguration.getChangeHistory().addModelUpdateListener(errorHandler);
        }
    }
}
