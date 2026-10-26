/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.nodeviews;

import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.pp.PosInSequent;

import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Extension adapter for showing hash codes for terms. Useful for debugging.
 *
 * @author Dominic Steinhoefel
 */
@KeYGuiExtension.Info( //
    name = "Show Hashcodes", //
    optional = true, //
    description = "GUI Extension for showing hash codes in tooltips", //
    experimental = false)
@NullMarked
public class ShowHashcodesExtension implements KeYGuiExtension, KeYGuiExtension.Tooltip {

    @Override
    public List<String> getTooltipStrings(MainWindow mainWindow, @Nullable PosInSequent pos) {
        if (pos == null || pos.isSequent()) {
            return Collections.emptyList();
        }

        String result = "";

        PosInOccurrence pio = pos.getPosInOccurrence();
        if (pio == null) {
            // a non-sequent position always carries its occurrence
            throw new NullPointerException("No position in occurrence available.");
        }
        final var term = pio.subTerm();
        result += "<b>Operator Hash:</b> " + term.op().hashCode();

        if (term.op() instanceof ElementaryUpdate) {
            result += "<br><b>LHS Hash:</b> " + ((ElementaryUpdate) term.op()).lhs().hashCode();
            result +=
                "<br><b>LHS Sort:</b> " + ((ElementaryUpdate) term.op()).lhs().sort();
        }

        return Collections.singletonList(result);
    }
}
