/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.util.List;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.pp.PosInSequent;

import org.key_project.logic.Term;


/**
 * Extension adapter for showing hash codes for terms, useful for debugging — FX port of
 * {@code de.uka.ilkd.key.gui.nodeviews.ShowHashcodesExtension} (Swing
 * ShowHashcodesExtension.java:20-45). The provider serves the {@link KeYGuiExtensionF.TooltipF}
 * capability (Swing {@code KeYGuiExtension.Tooltip}, KeYGuiExtension.java:186-201): for the
 * hovered sequent term it reports the hash code of the term's operator and — for
 * {@link ElementaryUpdate} operators — additionally the hash code and the sort of the update's
 * left-hand side (Swing {@code getTooltipStrings}, ShowHashcodesExtension.java:28-45). The
 * strings are aggregated by
 * {@link de.uka.ilkd.key.gui.fx.extension.KeYGuiExtensionFacadeF#getTooltipStrings} (Swing
 * {@code KeYGuiExtensionFacade.getTooltipStrings}, KeYGuiExtensionFacade.java:395-399) and
 * appended to the sequent-view hover tooltip by
 * {@code de.uka.ilkd.key.gui.fx.nodeviews.SequentViewF#getTooltipText} (Swing
 * {@code SequentView.getToolTipText}, SequentView.java:232-236; FX consumption P4, D30,
 * SequentViewF.java:1698-1706).
 * <p>
 * KNOWN-SIMPLIFIED: the Swing original returns one HTML string,
 * "{@code <b>Operator Hash:</b> &hellip;}" with "{@code <br>
 * }" separators
 * (ShowHashcodesExtension.java:36-44); the JavaFX tooltip is plain text (no HTML support), so
 * the FX port returns the same information as plain-text lines — the bold markers are dropped
 * and "{@code <br>
 * }" becomes a {@code '\n'} line break.
 * <p>
 * Like the Swing original the provider is stateless and instantiable without a running FX
 * toolkit; the mediator argument is unused (the Swing method ignores its {@code MainWindow}
 * argument too). Null and whole-sequent positions yield the empty list (Swing
 * ShowHashcodesExtension.java:29-31); a non-sequent position without a
 * {@link PosInSequent#getPosInOccurrence() PosInOccurrence} is also guarded to the empty list
 * (the Swing original would throw a NullPointerException there; the FX hover machinery only
 * passes positions with a sub term, SequentViewF.java:1692).
 *
 * @author Dominic Steinhoefl (Swing original)
 * @author MP9.0 extension SPI port (FX)
 */
@KeYGuiExtensionF.Info(name = "Show Hashcodes", optional = true,
    description = "GUI Extension for showing hash codes in tooltips", experimental = false)
public class ShowHashcodesExtensionF implements KeYGuiExtensionF, KeYGuiExtensionF.TooltipF {

    @Override
    public List<String> getTooltipStrings(KeYMediatorF mediator, PosInSequent pos) {
        if (pos == null || pos.isSequent() || pos.getPosInOccurrence() == null) {
            return List.of();
        }

        Term term = pos.getPosInOccurrence().subTerm();
        // KNOWN-SIMPLIFIED: Swing composes HTML ("<b>Operator Hash:</b> ..." with "<br>"
        // separators, ShowHashcodesExtension.java:33-44); the JavaFX tooltip is plain text
        // (no HTML support), so the same facts are returned as plain-text lines — the bold
        // markers are dropped and "<br>" becomes '\n'.
        String result = "Operator Hash: " + term.op().hashCode();

        if (term.op() instanceof ElementaryUpdate update) {
            result += "\nLHS Hash: " + update.lhs().hashCode();
            result += "\nLHS Sort: " + update.lhs().sort();
        }

        return List.of(result);
    }
}
