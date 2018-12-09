package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.gui.interactionlog.model.Interaction;
import de.uka.ilkd.key.gui.interactionlog.model.InteractionLog;
import de.uka.ilkd.key.logic.PosInOccurrence;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.bind.Unmarshaller;
import java.io.File;
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
    public static JAXBContext createContext() throws JAXBException {
        JAXBContext ctx = JAXBContext.newInstance(Interaction.class);
        return ctx;
    }

    public static InteractionLog readInteractionLog(File inputFile)
            throws JAXBException {
        JAXBContext ctx = createContext();
        Unmarshaller unmarshaller = ctx.createUnmarshaller();
        return (InteractionLog) unmarshaller.unmarshal(inputFile);
    }

    public static void storeInteractionLog(InteractionLog log, File output)
            throws JAXBException {
        JAXBContext ctx = createContext();
        Marshaller marshaller = ctx.createMarshaller();
        marshaller.marshal(log, output);
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
