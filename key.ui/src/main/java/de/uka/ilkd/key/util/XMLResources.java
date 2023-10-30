/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * An instance of this class loads several XML files, whose contents are displayed in
 * {@link de.uka.ilkd.key.gui.InfoView}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class XMLResources {

    private static final String RULE_RESOURCE = "/de/uka/ilkd/key/gui/help/ruleExplanations.xml";
    private static final Logger LOGGER = LoggerFactory.getLogger(XMLResources.class);
    protected final Properties ruleExplanations;

    private static final String LABEL_RESOURCE =
        "/de/uka/ilkd/key/gui/help/termLabelExplanations.xml";
    protected final Properties termLabelExplanations;

    static final String FUNCTION_RESOURCE = "/de/uka/ilkd/key/gui/help/functionExplanations.xml";
    protected final Properties functionExplanations;

    public XMLResources() {
        ruleExplanations = getResource(RULE_RESOURCE);
        termLabelExplanations = getResource(LABEL_RESOURCE);
        functionExplanations = getResource(FUNCTION_RESOURCE);
    }

    public Properties getRuleExplanations() {
        return ruleExplanations;
    }

    public Properties getTermLabelExplanations() {
        return termLabelExplanations;
    }

    public Properties getFunctionExplanations() {
        return functionExplanations;
    }

    private static Properties getResource(String xmlFile) {
        Properties ret = new Properties();

        try (InputStream is = XMLResources.class.getResourceAsStream(xmlFile)) {
            if (is == null) {
                throw new FileNotFoundException("Descriptions file " + xmlFile + " not found.");
            }
            ret.loadFromXML(is);
        } catch (IOException e) {
            LOGGER.error("Cannot not load help messages in info view", e);
        }

        return ret;
    }

}
