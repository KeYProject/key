package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.util.script.InteractionLog;

import java.beans.XMLDecoder;
import java.beans.XMLEncoder;
import java.io.*;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
public final class InteractionLogFacade {
    public static InteractionLog readInteractionLog(File inputFile)
            throws IOException {
        try (InputStream is = new FileInputStream(inputFile)) {
            XMLDecoder decoder = new XMLDecoder(is);
            return (InteractionLog) decoder.readObject();
        }
    }

    public static InteractionLog storeInteractionLog(InteractionLog log, File output)
            throws IOException {
        try (OutputStream os = new FileOutputStream(output)) {
            XMLEncoder encoder = new XMLEncoder(os);
            encoder.writeObject(log);
        }
    }
}
