package org.key_project.ui.interactionlog.algo;

import org.key_project.ui.interactionlog.model.InteractionLog;

import java.io.PrintWriter;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
public class KPSProofScriptExport extends MUProofScriptExport {
    public static void writeTo(InteractionLog logbook, PrintWriter writer) {
        writer.format("// Proof script: *%s*%n", logbook.getName());
        writer.format("// Created at *%s*%n", logbook.getCreated());
    }
}