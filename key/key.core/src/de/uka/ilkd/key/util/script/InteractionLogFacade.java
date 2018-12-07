package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.logic.PosInOccurrence;

import java.beans.XMLDecoder;
import java.beans.XMLEncoder;
import java.io.*;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

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
            encoder.writeObject(log);
        }
    }

    public static String serializePosInOccurence(PosInOccurrence p) {
        List<Integer> indices = new ArrayList<>();
        PosInOccurrence current = p;
        while (current != null) {
            indices.add(p.getIndex());
            current = current.up();
        }
        Collections.reverse(indices);
        return indices.stream().map(Objects::toString)
                .collect(Collectors.joining("."));
    }
}
