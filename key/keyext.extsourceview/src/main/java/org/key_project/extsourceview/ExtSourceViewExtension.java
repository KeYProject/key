package org.key_project.extsourceview;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.sourceview.SourceViewInsertion;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.java.declaration.ClassDeclaration;

import javax.annotation.Nonnull;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.io.IOException;
import java.net.URI;
import java.util.Collection;
import java.util.Collections;

@KeYGuiExtension.Info(name = "Extended Source View",
        description = "Author: Mike Schwörer <main@mikescher.com>",
        experimental = false,
        optional = true,
        priority = 10000)
public class ExtSourceViewExtension implements KeYGuiExtension, KeYGuiExtension.LeftPanel {

    private static final Logger LOGGER = LoggerFactory.getLogger(ExtSourceViewExtension.class);

    public static final String INSERTION_GROUP = "ExtSourceViewExtension::insertion";

    @Nonnull
    @Override
    public Collection<TabPanel> getPanels(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {

        // add a listener for changes in the proof tree
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                if (!mediator.isInAutoMode()) {
                    updateSourceview(window, mediator);
                }
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                updateSourceview(window, mediator);
            }
        });

        return Collections.emptyList();
    }

    private void updateSourceview(MainWindow window, KeYMediator mediator) {
        var svc = mediator.getServices();

        var tb = svc.getTermBuilder();

        var sourceView = window.getSourceViewFrame().getSourceView();

        var proof = mediator.getSelectedProof();

        var node = mediator.getSelectedNode();

        var sequent = node.sequent();

        var ante = sequent.antecedent();
        var succ = sequent.succedent();

        try {
            URI fileUri = sourceView.getSelectedFile(); // currently we support only proofs with a single file

            var contractPO = (FunctionalOperationContractPO)svc.getSpecificationRepository().getPOForProof(proof); //TODO type check

            var contract = contractPO.getContract();

            var progrMethod = contract.getTarget();

            var posStart = progrMethod.getPositionInfo().getStartPosition();
            var posEnd   = progrMethod.getPositionInfo().getEndPosition();

            sourceView.clearInsertion(fileUri, INSERTION_GROUP);

            var parts = ESVBuilder.extractParts(tb, sequent);

            for (var term: parts.get(InsertionType.REQUIRES_IMPLICT)) {

                var str = "        " + "//@ assume " + term.toJMLString(svc) + "; //(impl)";
                var col = new Color(0x0000c0); // TODO use ColorSettings: "[java]jml" ?
                var bkg = new Color(222, 222, 222);
                var ins = new SourceViewInsertion(INSERTION_GROUP, posStart.getLine()+1, str, col, bkg);

                sourceView.addInsertion(fileUri, ins);

            }

            sourceView.addInsertion(fileUri, new SourceViewInsertion(INSERTION_GROUP, posStart.getLine()+1, "", Color.BLACK, Color.WHITE));

            for (var term: parts.get(InsertionType.REQUIRES_EXPLICT)) {

                var str = "        " + "//@ assume " + term.toJMLString(svc) + ";";
                var col = new Color(0x0000c0); // TODO use ColorSettings: "[java]jml" ?
                var bkg = new Color(222, 222, 222);
                var ins = new SourceViewInsertion(INSERTION_GROUP, posStart.getLine()+1, str, col, bkg);

                sourceView.addInsertion(fileUri, ins);

            }

            for (var term: parts.get(InsertionType.ENSURES_IMPLICT)) {

                var str = "        " + "//@ assert " + term.toJMLString(svc) + "; //(impl)";
                var col = new Color(0x0000c0); // TODO use ColorSettings: "[java]jml" ?
                var bkg = new Color(222, 222, 222);
                var ins = new SourceViewInsertion(INSERTION_GROUP, posEnd.getLine(), str, col, bkg);

                sourceView.addInsertion(fileUri, ins);

            }

            sourceView.addInsertion(fileUri, new SourceViewInsertion(INSERTION_GROUP, posEnd.getLine(), "", Color.BLACK, Color.WHITE));

            for (var term: parts.get(InsertionType.ENSURES_EXPLICT)) {

                var str = "        " + "//@ assert " + term.toJMLString(svc) + ";";
                var col = new Color(0x0000c0); // TODO use ColorSettings: "[java]jml" ?
                var bkg = new Color(222, 222, 222);
                var ins = new SourceViewInsertion(INSERTION_GROUP, posEnd.getLine(), str, col, bkg);

                sourceView.addInsertion(fileUri, ins);

            }

        } catch (IOException | BadLocationException e) {
            LOGGER.error("Failed to update ExtSourceView", e);
        }

    }
}
