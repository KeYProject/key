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
public class DescriptionFacade {
    private static final String COMMANDS_DESCRIPTION = "commands_description.xml";
    private static Properties properties = null;

    private DescriptionFacade() {
    }

    /**
     * Lazy loading of the properties.
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
     * @param cmd
     * @return
     */
    public static String getDocumentation(ProofScriptCommand cmd) {
        return getString(cmd.getName());
    }

    /**
     * @param arg
     * @return
     */
    public static String getDocumentation(ProofScriptArgument arg) {
        String key = arg.getCommand().getName() + "." + arg.getName();
        return getString(key);
    }

    private static String getString(String key) {
        String property = getProperties().getProperty(key);
        if (null == property) {
            System.err.println("No documentation entry found for " + key + " in " + COMMANDS_DESCRIPTION);
            return "";
        }
        return property;
    }
}
