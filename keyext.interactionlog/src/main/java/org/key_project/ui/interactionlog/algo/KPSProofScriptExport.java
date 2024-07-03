/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.interactionlog.algo;

import java.io.PrintWriter;

import org.key_project.ui.interactionlog.model.InteractionLog;

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
