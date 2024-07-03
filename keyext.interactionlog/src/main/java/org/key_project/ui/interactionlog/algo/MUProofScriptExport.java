/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.interactionlog.algo;

import java.io.PrintWriter;
import java.io.StringWriter;

import org.key_project.ui.interactionlog.api.Interaction;
import org.key_project.ui.interactionlog.model.InteractionLog;
import org.key_project.ui.interactionlog.model.NodeIdentifier;
import org.key_project.ui.interactionlog.model.NodeInteraction;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
public class MUProofScriptExport {
    public static void writeTo(InteractionLog logbook, PrintWriter writer) {
        writer.format("// Proof script: *%s*%n", logbook.getName());
        writer.format("// Created at *%s*%n", logbook.getCreated());
        logbook.getInteractions().forEach(it -> {
            writeSelector(writer, it);
            writer.write(it.getProofScriptRepresentation());
        });
    }

    private static void writeSelector(PrintWriter out, Interaction it) {
        try {
            NodeIdentifier id = ((NodeInteraction) it).getNodeId();
            if (id != null)
                out.format("select %s;%n", id.getBranchLabel());
        } catch (ClassCastException ignored) {
        }
    }

    public static String getScript(InteractionLog current) {
        StringWriter sw = new StringWriter();
        writeTo(current, new PrintWriter(sw));
        return sw.toString();
    }
}
