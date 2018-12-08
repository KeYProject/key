package de.uka.ilkd.key.gui.interactionlog;

import java.beans.XMLDecoder;
import java.beans.XMLEncoder;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uka.ilkd.key.gui.interactionlog.model.InteractionLog;
import de.uka.ilkd.key.logic.PosInOccurrence;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
public final class InteractionLogFacade {
    public static InteractionLog readInteractionLog(File inputFile)
            throws IOException {
        try (InputStream is = new FileInputStream(inputFile);
             XMLDecoder decoder = new XMLDecoder(is)) {
            return (InteractionLog) decoder.readObject();
        }
    }

    public static void storeInteractionLog(InteractionLog log, File output)
            throws IOException {
        try (OutputStream os = new FileOutputStream(output);
             XMLEncoder encoder = new XMLEncoder(os)) {
            encoder.setExceptionListener(e -> {
                e.printStackTrace();
            });
            encoder.writeObject(log);
        } catch(Exception e) {
            System.err.println(e.getMessage());
        }
    }

    public static String serializePosInOccurence(PosInOccurrence p) {
        List<Integer> indices = new ArrayList<>();
        PosInOccurrence current = p;

        while (current != null && !current.isTopLevel()) {
            indices.add(p.getIndex());
            current = current.up();
        }

        Collections.reverse(indices);
        return indices.stream().map(Objects::toString)
                .collect(Collectors.joining("."));
    }
}
