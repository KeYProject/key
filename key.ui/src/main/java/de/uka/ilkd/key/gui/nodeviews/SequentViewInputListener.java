/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.*;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.io.IOException;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.StringJoiner;
import java.util.stream.Collectors;
import javax.swing.*;
import javax.swing.text.BadLocationException;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceView.Highlight;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.FileOrigin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class implements all input listener interfaces for SequentView.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class SequentViewInputListener implements MouseMotionListener, MouseListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(SequentViewInputListener.class);

    /**
     * The color for origin highlights.
     *
     * @see #highlightOriginInSourceView(PosInSequent)
     */
    private static final ColorSettings.ColorProperty ORIGIN_HIGHLIGHT_COLOR = ColorSettings.define(
        "[SourceView]originHighlight",
        "Color for highlighting origin of selected term in source view", new Color(252, 202, 80));

    /**
     * The color for subterm origin highlights.
     *
     * @see #highlightOriginInSourceView(PosInSequent)
     */
    private static final ColorSettings.ColorProperty SUBTERM_ORIGIN_HIGHLIGHT_COLOR =
        ColorSettings.define("[SourceView]originHighlight",
            "Color for highlighting origin of subterms of selected term in source view",
            new Color(252, 228, 169));

    /**
     * The current origin highlights.
     *
     * @see #highlightOriginInSourceView(PosInSequent)
     */
    private final Set<Highlight> originHighlights = new HashSet<>();

    /** The sequent view associated with this listener. */
    private final SequentView sequentView;

    /** Whether term info should be shown in the status line. */
    private final boolean showTermInfo = false;

    /** @see #isRefresh() */
    private static boolean refresh = true;

    /**
     * @return whether this listener should react to changes.
     */
    public static boolean isRefresh() {
        return refresh;
    }

    public static void setRefresh(boolean refresh) {
        SequentViewInputListener.refresh = refresh;
    }

    SequentViewInputListener(SequentView sequentView) {
        this.sequentView = sequentView;
    }

    @Override
    public void mouseDragged(MouseEvent me) {
        // This method is required by MouseMotionListener interface.
    }

    @Override
    public void mouseMoved(MouseEvent me) {
        showTermInfo(me.getPoint());
        if (sequentView.refreshHighlightning && refresh
                && sequentView.getDocument().getLength() > 0) {
            sequentView.highlight(me.getPoint());
        }

        if (sequentView.isInUserSelectionHighlight(null)) {
            highlightOriginInSourceView(sequentView.getPosInSequent(me.getPoint()));
        }
    }

    @Override
    public void mouseExited(MouseEvent e) {
        if (sequentView.refreshHighlightning) {
            sequentView.disableHighlights();
        }

        if (sequentView.isInUserSelectionHighlight(null)) {
            highlightOriginInSourceView(null);
        }
    }

    @Override
    public void mouseClicked(MouseEvent e) {
        if (!sequentView.isMainSequentView()) {
            return;
        }

        if (SwingUtilities.isMiddleMouseButton(e)
                || e.isControlDown() && SwingUtilities.isLeftMouseButton(e)) {
            Point point = e.getPoint();
            PosInSequent pis = sequentView.getPosInSequent(point);

            if (pis == null || pis.isSequent() || sequentView.isInUserSelectionHighlight(point)) {
                sequentView.removeUserSelectionHighlight();
            } else {
                sequentView.setUserSelectionHighlight(point);
            }
        }
    }

    @Override
    public void mousePressed(MouseEvent e) {}

    @Override
    public void mouseReleased(MouseEvent e) {}

    @Override
    public void mouseEntered(MouseEvent e) {}

    /**
     * Highlights the origin of the term at the specified position.
     *
     * @param pos the position of the term whose origin should be highlighted.
     */
    public void highlightOriginInSourceView(PosInSequent pos) {
        if (!ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isHighlightOrigin()) {
            // Don't highlight anything and delete existing highlights.
            pos = null;
        }

        SourceView sourceView = SourceView.getSourceView(sequentView.getMainWindow());

        originHighlights.forEach(sourceView::removeHighlight);
        originHighlights.clear();

        if (pos == null || pos.getPosInOccurrence() == null) {
            return;
        }

        FileOrigin origin;
        Set<FileOrigin> subtermOrigins;

        Term term = pos.getPosInOccurrence().subTerm();
        OriginTermLabel label = (OriginTermLabel) term.getLabel(OriginTermLabel.NAME);

        if (label == null) {
            Origin or = OriginTermLabel.getOrigin(pos);

            origin = or instanceof FileOrigin ? (FileOrigin) or : null;
            subtermOrigins = Collections.emptySet();
        } else {
            Origin or = label.getOrigin();

            origin = or instanceof FileOrigin ? (FileOrigin) or : null;
            subtermOrigins = label.getSubtermOrigins().stream().filter(o -> o instanceof FileOrigin)
                    .map(o -> (FileOrigin) o).collect(Collectors.toSet());
        }

        try {
            if (origin != null) {
                originHighlights.addAll(
                    sourceView.addHighlightsForJMLStatement(origin.getFileName().orElse(null),
                        origin.getLine(), ORIGIN_HIGHLIGHT_COLOR.get(), 20));
            }

            for (FileOrigin subtermOrigin : subtermOrigins) {
                if (!subtermOrigin.equals(origin)) {
                    originHighlights
                            .addAll(sourceView.addHighlightsForJMLStatement(
                                subtermOrigin.getFileName().orElse(null),
                                subtermOrigin.getLine(), SUBTERM_ORIGIN_HIGHLIGHT_COLOR.get(), 10));
                }
            }
        } catch (BadLocationException | IOException e) {
            LOGGER.warn("Failed to read or set location", e);
        }
    }

    /**
     * Show info about the term at the specified point in the status line.
     *
     * @param p a point.
     */
    protected void showTermInfo(Point p) {
        MainWindow mainWindow = sequentView.getMainWindow();

        if (showTermInfo) {
            PosInSequent mousePos = sequentView.getPosInSequent(p);
            String info = null;

            if ((mousePos != null) && !("".equals(sequentView.getHighlightedText(mousePos)))) {

                Term t;
                final PosInOccurrence posInOcc = mousePos.getPosInOccurrence();
                if (posInOcc != null) {
                    t = posInOcc.subTerm();
                    String tOpClassString = t.op().getClass().toString();
                    String operator = tOpClassString.substring(tOpClassString.lastIndexOf('.') + 1);
                    // The hash code is displayed here since sometimes terms with
                    // equal string representation are still different.
                    info = operator + ", Sort: " + t.sort() + ", Hash:" + t.hashCode();

                    Sequent seq =
                        sequentView.getMainWindow().getMediator().getSelectedNode().sequent();
                    info += ProofSaver.posInOccurrence2Proof(seq, posInOcc);

                    StringJoiner extensionStr = new StringJoiner(", ", ", ", "");
                    extensionStr.setEmptyValue("");
                    KeYGuiExtensionFacade.getTermInfoStrings(sequentView.getMainWindow(), mousePos)
                            .forEach(extensionStr::add);
                    info += extensionStr;
                }
            }

            if (info == null) {
                mainWindow.setStandardStatusLine();
            } else {
                mainWindow.setStatusLine(info);
            }
        }
    }

}
