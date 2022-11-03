package org.key_project.extsourceview;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceViewInsertion;
import de.uka.ilkd.key.logic.origin.OriginRef;
import org.key_project.extsourceview.transformer.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.text.BadLocationException;
import java.awt.*;
import java.io.IOException;
import java.net.URI;

public class SourceViewPatcher {

    private static final Logger LOGGER = LoggerFactory.getLogger(SourceViewPatcher.class);

    public static final String INSERTION_GROUP = "ExtSourceViewExtension::insertion";

    private final static Color COL_HIGHLIGHT_MAIN = new Color(255, 0, 255);
    private final static Color COL_HIGHLIGHT_CHILDS = new Color(255, 128, 255);

    private final static String HL_KEY = "SourceViewPatcher::highlight";

    private final static int HIGHTLIGHT_LEVEL = 11;

    public static void updateSourceview(MainWindow window, KeYMediator mediator,
            boolean hideNonRelevant, boolean continueOnError)
            throws TransformException, InternTransformException {

        SourceView sourceView = window.getSourceViewFrame().getSourceView();
        URI fileUri = sourceView.getSelectedFile(); // currently we support only proofs with a
                                                    // single file

        try {
            sourceView.clearInsertion(fileUri, INSERTION_GROUP);
        } catch (IOException | BadLocationException e) {
            throw new InternTransformException("Failed to clear existing insertions", e);
        }

        SequentBackTransformer transformer = new SequentBackTransformer(mediator.getServices(),
            mediator.getSelectedProof(), mediator.getSelectedNode());

        TermTranslator translator = new TermTranslator(mediator.getServices());

        InsertionSet parts = transformer.extract(continueOnError);

        PositionMap posmap = transformer.generatePositionMap();

        for (var iterm : parts.get()) {

            if (!iterm.IsRevelant() && hideNonRelevant)
                continue;

            int line = posmap.getLineForInsTerm(iterm);

            int indentation = posmap.getLineIndent(line);

            String jmlstr =
                " ".repeat(indentation) + (continueOnError ? translator.translateSafe(iterm)
                        : translator.translate(iterm));

            try {
                addInsertion(sourceView, fileUri, line, iterm, jmlstr);
            } catch (IOException | BadLocationException e) {
                throw new InternTransformException("Failed to add insertion", e);
            }
        }
    }

    private static void addInsertion(SourceView sv, URI fileUri, int line, InsertionTerm ins,
            String str) throws IOException, BadLocationException {
        Color col = new Color(0x0000c0); // TODO use ColorSettings: "[java]jml" ?
        Color bkg = new Color(222, 222, 222);

        if (ins.Type == InsertionType.ASSERT_ERROR || ins.Type == InsertionType.ASSUME_ERROR) {
            col = new Color(0xCC0000);
        }

        SourceViewInsertion svi = new SourceViewInsertion(INSERTION_GROUP, line, str, col, bkg);

        var originRefs = Utils.getSubOriginRefs(ins.Term, true, true);

        svi.addMouseEnterListener(e -> {

            try {
                for (OriginRef orig : originRefs) {
                    if (!orig.hasFile() || !sv.hasFile(orig.fileURI()))
                        continue;

                    if (orig.LineStart == orig.LineEnd) {
                        sv.addHighlight(orig.fileURI(), HL_KEY, orig.LineStart, orig.ColumnStart,
                            orig.ColumnEnd, COL_HIGHLIGHT_MAIN, HIGHTLIGHT_LEVEL);
                    } else {
                        for (int i = orig.LineStart; i <= orig.LineEnd; i++) {
                            sv.addHighlight(orig.fileURI(), HL_KEY, i, COL_HIGHLIGHT_MAIN,
                                HIGHTLIGHT_LEVEL);
                        }
                    }
                }
            } catch (IOException | BadLocationException ex) {
                LOGGER.error("failed to add highlight", ex);
            }
        });
        svi.addMouseLeaveListener(e -> sv.removeHighlights(HL_KEY));

        sv.addInsertion(fileUri, svi);
    }
}
