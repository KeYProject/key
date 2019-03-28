package org.key_project.ui.interactionlog.algo;

import org.key_project.ui.interactionlog.model.Interaction;
import org.key_project.ui.interactionlog.model.InteractionLog;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
public class StreamInteractionVisitor extends DefaultInteractionVisitor<Void> {
    protected PrintWriter out;

    public StreamInteractionVisitor() {
    }

    public StreamInteractionVisitor(PrintWriter out) {
        this.out = out;
    }


    public static String translate(StreamInteractionVisitor visitor, Interaction interaction) {
        try (StringWriter sw = new StringWriter()) {
            visitor.out = new PrintWriter(sw);
            interaction.accept(visitor);
            return sw.toString();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return null;
    }

    public static void translate(
            StreamInteractionVisitor visitor,
            InteractionLog logbook) {
        logbook.getInteractions().forEach(interaction -> interaction.accept(visitor));
    }
}


