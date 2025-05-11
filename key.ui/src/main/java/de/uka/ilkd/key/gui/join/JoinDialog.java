/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.join;

import java.awt.*;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.InspectorForDecisionPredicates;
import de.uka.ilkd.key.gui.utilities.CheckedUserInput;
import de.uka.ilkd.key.gui.utilities.CheckedUserInput.CheckedUserInputInspector;
import de.uka.ilkd.key.gui.utilities.CheckedUserInput.CheckedUserInputListener;
import de.uka.ilkd.key.gui.utilities.ClickableMessageBox;
import de.uka.ilkd.key.gui.utilities.InspectorForFormulas;
import de.uka.ilkd.key.gui.utilities.StdDialog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.delayedcut.ApplicationCheck;
import de.uka.ilkd.key.proof.delayedcut.DelayedCut;
import de.uka.ilkd.key.proof.delayedcut.DelayedCutProcessor;
import de.uka.ilkd.key.proof.join.LateApplicationCheck;
import de.uka.ilkd.key.proof.join.PredicateEstimator;
import de.uka.ilkd.key.proof.join.PredicateEstimator.Result;
import de.uka.ilkd.key.proof.join.ProspectivePartner;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public class JoinDialog extends StdDialog {
    private static final Color GREEN = new Color(0, 128, 0);

    private static final long serialVersionUID = 1L;
    private final @NonNull ContentPanel content;

    public JoinDialog(@NonNull List<ProspectivePartner> partnerList, @NonNull Proof proof,
            PredicateEstimator estimator, @NonNull Services services) {
        super("Joining", 5, false);
        content = new ContentPanel(partnerList, proof, estimator,
            (input, valid, reason) -> getOkButton().setEnabled(valid), services);
        this.setContent(content);

    }

    private static final String INFO = """
            It is not possible to join both goals, because new symbols have been introduced
             on the branches which belong to the goals: Up to now the treatment of new symbols
            is not supported by the joining mechanism.

            """;


    private static class ContentPanel extends Box {
        private static final long serialVersionUID = 1L;

        private SequentViewer sequentViewer1;
        private SequentViewer sequentViewer2;
        private JList<ContentItem> choiceList;
        private CheckedUserInput predicateInput;
        private JLabel joinHeadline;
        private JLabel infoPredicate;
        private ClickableMessageBox infoBox;
        private @Nullable JScrollPane infoBoxPane = null;

        private final @NonNull Proof proof;
        private final PredicateEstimator estimator;

        // private JTextPane inputPredicate;

        private static class ContentItem {
            final @NonNull ProspectivePartner partner;
            final @NonNull CheckedUserInputInspector inspector;
            final boolean applicable;

            public ContentItem(@NonNull ProspectivePartner partner, @NonNull Services services,
                    boolean applicable) {
                super();
                this.partner = partner;
                this.inspector = new InspectorForDecisionPredicates(services,
                    partner.getCommonParent(), DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT,
                    DelayedCutProcessor.getApplicationChecks());
                this.applicable = applicable;
            }

            public @NonNull CheckedUserInputInspector getInspector() {
                return inspector;
            }



            public boolean isApplicable() {
                return applicable;
            }

            @NonNull
            Sequent getSequent() {
                return partner.getNode(1).sequent();
            }

            @Override
            public @NonNull String toString() {
                return "Goal " + partner.getNode(1).serialNr();
            }

            public @NonNull String getPredicateInfo() {
                return "Decision Formula (true for Goal " + partner.getNode(0).serialNr()
                    + ", false for Goal " + partner.getNode(1).serialNr() + ")";
            }

            public @NonNull String getPredicate(@NonNull Proof proof) {
                if (partner.getCommonPredicate() == null) {
                    return "";
                }
                LogicPrinter printer =
                    LogicPrinter.purePrinter(new NotationInfo(), proof.getServices());
                printer.printTerm(partner.getCommonPredicate());
                return printer.result();
            }
        }


        public ContentPanel(@NonNull List<ProspectivePartner> partnerList,
                final @NonNull Proof proof,
                PredicateEstimator estimator, final @NonNull CheckedUserInputListener listener,
                @NonNull Services services) {
            super(BoxLayout.Y_AXIS);

            this.proof = proof;
            this.estimator = estimator;
            create();

            getPredicateInput().addListener((input, valid, reason) -> {
                if (valid) {
                    getSelectedPartner().setCommonPredicate(
                        InspectorForFormulas.translate(proof.getServices(), input));
                    listener.userInputChanged(input, getSelectedItem().isApplicable(), reason);
                } else {
                    listener.userInputChanged(input, false, reason);
                }
                refreshInfoBox(reason);
            });


            if (!partnerList.isEmpty()) {
                fill(partnerList, services);
            }

        }

        private void fill(@NonNull List<ProspectivePartner> partnerList,
                @NonNull Services services) {
            Node node = partnerList.get(0).getNode(0);
            getHeadline().setText("<html><b>Join Goal " + node.serialNr() + "</b></html>");
            getSequentViewer1().setSequent(node.sequent(), proof.getServices());



            DefaultListModel<ContentItem> model = new DefaultListModel<>();
            for (final ProspectivePartner partner : partnerList) {

                Result result = estimator.estimate(partner, proof);
                partner.setCommonPredicate(result.getPredicate());
                partner.setCommonParent(result.getCommonParent());


                ApplicationCheck check = new ApplicationCheck.NoNewSymbolsCheck();

                boolean applicable = true;
                applicable = LateApplicationCheck.INSTANCE
                        .check(partner.getNode(0), result.getCommonParent(), check).isEmpty()
                        && applicable;
                applicable = LateApplicationCheck.INSTANCE
                        .check(partner.getNode(1), result.getCommonParent(), check).isEmpty()
                        && applicable;

                model.addElement(new ContentItem(partner, services, applicable));
            }


            getChoiceList().setModel(model);
            getChoiceList().setSelectedIndex(0);


        }

        private void selectionChanged(int index) {
            if (index < 0 || index > getChoiceList().getModel().getSize()) {
                return;
            }
            ContentItem item = choiceList.getModel().getElementAt(index);
            getSequentViewer2().setSequent(item.getSequent(), proof.getServices());


            getPredicateInput().setInput(item.getPredicate(proof));
            getPredicateInput().setInspector(item.getInspector());
            getInfoPredicate().setText(item.getPredicateInfo());

        }

        private @NonNull Box createLeftAlignedComponent(JComponent comp) {

            Box box = Box.createHorizontalBox();
            box.add(comp);
            box.add(Box.createHorizontalGlue());
            return box;
        }

        private void create() {


            Box box = Box.createHorizontalBox();


            box.add(getHeadline());
            box.add(Box.createHorizontalGlue());


            this.add(Box.createVerticalStrut(5));
            this.add(box);
            this.add(Box.createVerticalStrut(5));


            box = Box.createHorizontalBox();
            Box vertBox = Box.createVerticalBox();
            vertBox.add(createLeftAlignedComponent(getHeadline()));
            vertBox.add(new JScrollPane(getSequentViewer1()));
            box.add(vertBox);


            vertBox = Box.createVerticalBox();
            JLabel label = new JLabel("<html><b>with</b></html>");


            label.setFont(this.getFont());
            vertBox.add(createLeftAlignedComponent(label));

            Box horzBox = Box.createHorizontalBox();
            horzBox.add(new JScrollPane(getChoiceList()));
            horzBox.add(Box.createHorizontalStrut(5));
            horzBox.add(new JScrollPane(getSequentViewer2()));
            vertBox.add(horzBox);
            box.add(vertBox);

            this.add(box);

            this.add(Box.createVerticalStrut(5));

            this.add(createLeftAlignedComponent(getInfoPredicate()));
            this.add(getPredicateInput());
            this.add(Box.createVerticalStrut(5));
            this.add(getInfoBoxPane());
            this.add(Box.createVerticalStrut(5));



        }

        private void refreshInfoBox(@Nullable String reason) {
            ContentItem item = getSelectedItem();
            getInfoBox().clear();
            if (!item.isApplicable()) {
                getInfoBox()
                        .add(INFO,
                            "Goal " + item.partner.getNode(0).serialNr() + " and " + "Goal "
                                + item.partner.getNode(1).serialNr() + " cannot be joined.",
                            Color.RED);

            } else if (reason != null) {
                String[] segments = reason.split("#");
                getInfoBox().add(segments.length > 1 ? segments[1] : null, segments[0], Color.RED);
            } else {
                getInfoBox().add(null, "Join is applicable.", GREEN);
            }

        }

        private JComponent getInfoBoxPane() {

            if (infoBoxPane == null) {

                infoBoxPane = new JScrollPane(getInfoBox());
                infoBoxPane.setBorder(BorderFactory.createTitledBorder("Details"));
                int height = getInfoBox().getFontMetrics(getInfoBox().getFont()).getHeight() * 4;
                infoBoxPane.setMaximumSize(new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE));
                infoBoxPane.setPreferredSize(new Dimension(0, height));
            }
            return infoBoxPane;
        }

        private ClickableMessageBox getInfoBox() {
            if (infoBox == null) {
                infoBox = new ClickableMessageBox();


                infoBox.setBackground(this.getBackground());

                infoBox.add(object -> JOptionPane.showMessageDialog(infoBox, object.toString(),
                    "Problem Description", JOptionPane.INFORMATION_MESSAGE));

            }
            return infoBox;
        }


        private JLabel getInfoPredicate() {
            if (infoPredicate == null) {
                infoPredicate = new JLabel(" ");
                infoPredicate.setFont(this.getFont());
            }
            return infoPredicate;
        }

        private @NonNull CheckedUserInput getPredicateInput() {
            if (predicateInput == null) {
                predicateInput = new CheckedUserInput(false);
            }
            return predicateInput;
        }

        private JList<ContentItem> getChoiceList() {
            if (choiceList == null) {
                choiceList = new JList<>();
                choiceList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
                choiceList.setPreferredSize(new Dimension(100, 300));
                choiceList.addListSelectionListener(
                    e -> selectionChanged(choiceList.getSelectedIndex()));
            }
            return choiceList;
        }

        private JLabel getHeadline() {
            if (joinHeadline == null) {
                joinHeadline = new JLabel("Join");
                joinHeadline.setFont(this.getFont());
                joinHeadline.setAlignmentX(LEFT_ALIGNMENT);
            }
            return joinHeadline;
        }


        private SequentViewer getSequentViewer1() {
            if (sequentViewer1 == null) {
                sequentViewer1 = new SequentViewer();
                sequentViewer1.setPreferredSize(new Dimension(400, 200));

            }
            return sequentViewer1;
        }

        private SequentViewer getSequentViewer2() {
            if (sequentViewer2 == null) {
                sequentViewer2 = new SequentViewer();
                sequentViewer2.setPreferredSize(new Dimension(300, 300));
            }
            return sequentViewer2;
        }

        public @NonNull ProspectivePartner getSelectedPartner() {
            return getSelectedItem().partner;
        }

        public ContentItem getSelectedItem() {
            int index = getChoiceList().getSelectedIndex();
            return getChoiceList().getModel().getElementAt(index);
        }

    }

    public @NonNull ProspectivePartner getSelectedPartner() {

        return content.getSelectedPartner();
    }



}
