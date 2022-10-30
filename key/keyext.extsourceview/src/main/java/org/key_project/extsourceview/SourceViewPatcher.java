package org.key_project.extsourceview;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceViewInsertion;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import org.key_project.extsourceview.transformer.InsertionTerm;
import org.key_project.extsourceview.transformer.SequentBackTransformer;
import org.key_project.extsourceview.transformer.InsertionType;
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

    public static void updateSourceview(MainWindow window, KeYMediator mediator) {
        Services svc = mediator.getServices();

        TermBuilder tb = svc.getTermBuilder();

        SourceView sourceView = window.getSourceViewFrame().getSourceView();

        Proof proof = mediator.getSelectedProof();

        Node node = mediator.getSelectedNode();

        Sequent sequent = node.sequent();

        try {
            URI fileUri = sourceView.getSelectedFile(); // currently we support only proofs with a single file

            var contractPO = (FunctionalOperationContractPO)svc.getSpecificationRepository().getPOForProof(proof); //TODO type check

            var contract = contractPO.getContract();

            var progrMethod = contract.getTarget();

            var posStart = progrMethod.getPositionInfo().getStartPosition();
            var posEnd   = progrMethod.getPositionInfo().getEndPosition();

            sourceView.clearInsertion(fileUri, INSERTION_GROUP);

            var parts = SequentBackTransformer.extractParts(tb, sequent);

            for (var term: parts.get(InsertionType.REQUIRES_IMPLICT)) {
                addInsertion(sourceView, fileUri, posEnd.getLine(), term, "//@ assume " + term.toJMLString(svc) + "; //(impl)");
            }

            sourceView.addInsertion(fileUri, new SourceViewInsertion(INSERTION_GROUP, posStart.getLine()+1, "", Color.BLACK, Color.WHITE));

            for (var term: parts.get(InsertionType.REQUIRES_EXPLICT)) {
                addInsertion(sourceView, fileUri, posEnd.getLine(), term, "//@ assume " + term.toJMLString(svc) + ";");
            }

            for (var term: parts.get(InsertionType.ENSURES_IMPLICT)) {
                addInsertion(sourceView, fileUri, posEnd.getLine(), term, "//@ assert " + term.toJMLString(svc) + "; //(impl)");
            }

            sourceView.addInsertion(fileUri, new SourceViewInsertion(INSERTION_GROUP, posEnd.getLine(), "", Color.BLACK, Color.WHITE));

            for (var term: parts.get(InsertionType.ENSURES_EXPLICT)) {
                addInsertion(sourceView, fileUri, posEnd.getLine(), term, "//@ assert " + term.toJMLString(svc) + ";");
            }

        } catch (IOException | BadLocationException e) {
            //TODO poper error handling
            LOGGER.error("Failed to update ExtSourceView", e);
        }

    }

    private static void addInsertion(SourceView sv, URI fileUri, int line, InsertionTerm ins, String termstr) throws IOException, BadLocationException {
        String str = "        " + termstr; //TODO determine indentation
        Color col = new Color(0x0000c0); // TODO use ColorSettings: "[java]jml" ?
        Color bkg = new Color(222, 222, 222);
        SourceViewInsertion svi = new SourceViewInsertion(INSERTION_GROUP, line, str, col, bkg);

        var originRefs = Utils.getSubOriginRefs(ins.Term, true, true);

        svi.addMouseEnterListener(e -> {

            try {
                for (OriginRef orig : originRefs) {
                    if (!orig.hasFile() || !sv.hasFile(orig.fileURI())) continue;

                    if (orig.LineStart == orig.LineEnd) {
                        sv.addHighlight(orig.fileURI(), HL_KEY, orig.LineStart, orig.ColumnStart, orig.ColumnEnd, COL_HIGHLIGHT_MAIN, HIGHTLIGHT_LEVEL);
                    } else {
                        for (int i = orig.LineStart; i <= orig.LineEnd; i++) {
                            sv.addHighlight(orig.fileURI(), HL_KEY, i, COL_HIGHLIGHT_MAIN, HIGHTLIGHT_LEVEL);
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
