package de.uka.ilkd.key.macros.scripts.meta;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

import java.io.IOException;
import java.util.Properties;

/**
 * This facade is used to load documentation for {@link ProofScriptCommand} and
 * {@link ProofScriptArgument}.
 * <p>
 * It uses a {@code COMMANDS_DESCRIPTION} property file.
 *
 * @author Alexander Weigl
 * @version 1 (18.08.17)
 */
public final class DescriptionFacade {
    /**
     * The filename of the XML properties containing the documentation of proof script commands.
     */
    private static final String COMMANDS_DESCRIPTION = "commands_description.xml";

    /**
     * Lazy-loaded properties
     *
     * @see #getProperties
     */
    private static Properties properties = null;

    private DescriptionFacade() {
    }

    /**
     * Lazy loading of the properties.
     *
     * @return a properties
     */
    public static Properties getProperties() {
        try {
            if (properties == null) {
                properties = new Properties();
                properties.loadFromXML(
                        DescriptionFacade.class.getResourceAsStream(COMMANDS_DESCRIPTION));
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        return properties;
    }

    /**
     * Looks up the documentation for the given command in the properties file.
     * If no documentation is available an empty string is returned.
     *
     * @param cmd non-null proof script command
     * @return a non-null string
     * @see ProofScriptCommand#getDocumentation()
     */
    public static String getDocumentation(ProofScriptCommand<?> cmd) {
        return getString(cmd.getName());
    }

    /**
     * Looks up the documentation for the given proof script argument.
     * If no documentation is available an empty string is returned.
     *
     * @param arg non-null proof script argument
     * @return a string or null, if {@code arg} is null or {@code arg.getCommand} returns null
     * @see ProofScriptArgument#getDocumentation()
     */
    public static String getDocumentation(ProofScriptArgument<?> arg) {
        if(arg==null || arg.getCommand() == null) {
            return null;
        }
        String key = arg.getCommand().getName() + "." + arg.getName();
        return getString(key);
    }

    /**
     * Helper function for look ups in the property file.
     *
     * @param key look up key
     * @return a non-null string
     */
    private static String getString(String key) {
        String property = getProperties().getProperty(key);
        if (null == property) {
            System.err.format("No documentation entry found for %s in %s%n",
                    key, COMMANDS_DESCRIPTION);
            return "";
        }
        return property;
    }
}
