package de.uka.ilkd.key.macros.scripts.meta;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

import java.io.IOException;
import java.util.Properties;

/**
 * @author Alexander Weigl
 * @version 1 (18.08.17)
 */
public class DescriptionFacade {
    private static final String COMMANDS_DESCRIPTION = "commands_description.xml";
    private static Properties properties = null;

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

    public static String getDocumentation(ProofScriptCommand cmd) {
        return getString(cmd.getName());
    }

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
