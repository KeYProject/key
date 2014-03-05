package de.uka.ilkd.key.gui;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

/**
 * Use this class to get descriptions from an XML file.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class XMLProperties extends Properties {

    XMLProperties(String xmlFile) {
        InputStream is = getClass().getResourceAsStream(xmlFile);
        try {
            if (is == null) {
                throw new FileNotFoundException("Descriptions file " + xmlFile + " not found.");
            }
            loadFromXML(is);
        } catch (IOException e) {
            System.err.println("Cannot not load help messages in info view");
            e.printStackTrace();
        }
    }
}
