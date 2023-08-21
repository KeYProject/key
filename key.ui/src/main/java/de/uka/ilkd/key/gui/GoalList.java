/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.ArrayList;
import java.util.EventObject;
import java.util.List;
import java.util.WeakHashMap;
import javax.swing.*;
import javax.swing.event.ListDataEvent;
import javax.swing.event.ListDataListener;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.gui.prooftree.DisableGoal;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.*;

import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class GoalList extends JList<Goal> implements TabPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(GoalList.class);

    public static final Icon GOAL_LIST_ICON = IconFontSwing
            .buildIcon(FontAwesomeSolid.FLAG_CHECKERED, MainWindow.TAB_ICON_SIZE);
    /**
     *
     */
    private static final long serialVersionUID = 1632264315383703798L;
    private final static ImageIcon keyIcon = IconFactory.keyHole(20, 20);
    private final static Icon disabledGoalIcon = IconFactory.keyHoleInteractive(20, 20);
    private final static Icon linkedGoalIcon = IconFactory.keyHoleLinked(20, 20);
    private final static int MAX_DISPLAYED_SEQUENT_LENGTH = 100;
    /**
     * the model used by this view
     */
    private final SelectingGoalListModel selectingListModel;
    private final GoalListModel goalListModel;
    // clear this cache whenever some display settings are changed?
    private final WeakHashMap<Sequent, String> seqToString = new WeakHashMap<>();
    private KeYMediator mediator;
    /**
     * interactive prover listener
     */
    private final GoalListInteractiveListener interactiveListener;
    /**
     * KeYSelection-Listener
     */
    private final GoalListSelectionListener selectionListener;
    /**
     * listens to gui events
     */
    private final GoalListGUIListener guiListener;

    public GoalList(KeYMediator mediator) {
        this();
        setMediator(mediator);
    }

    public GoalList() {
        interactiveListener = new GoalListInteractiveListener();
        selectionListener = new GoalListSelectionListener();
        guiListener = new GoalListGUIListener();

        setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        goalListModel = new GoalListModel();
        selectingListModel = new SelectingGoalListModel(goalListModel);
        setModel(selectingListModel);
        setCellRenderer(new IconCellRenderer());
        addListSelectionListener(new GoalListSelectionListern());

        MouseListener ml = new MouseAdapter() {
            public void mousePressed(MouseEvent e) {
                setSelectedIndex(locationToIndex(e.getPoint()));
                if (e.isPopupTrigger()) {
                    popupMenu().show(e.getComponent(), e.getX(), e.getY());
                }
            }

            // Thanks to Windows nonsense
            public void mouseReleased(MouseEvent e) {
                mousePressed(e);
            }
        };
        addMouseListener(ml);

        updateUI();
        KeYGuiExtensionFacade.installKeyboardShortcuts(mediator, this,
            KeYGuiExtension.KeyboardShortcuts.GOAL_LIST);
    }

    @Override
    public String getTitle() {
        return "Goals";
    }

    @Override
    public Icon getIcon() {
        return GOAL_LIST_ICON;
    }

    @Override
    public JComponent getComponent() {
        return new JScrollPane(this);
    }

    private JPopupMenu popupMenu() {
        JPopupMenu menu = new JPopupMenu();

        menu.add(new DisableSingleGoal());
        menu.add(new DisableOtherGoals());

        return menu;
    }

    /**
     * set the KeYMediator
     */
    private void setMediator(KeYMediator m) {
        if (mediator != null) {
            unregister();
        }
        mediator = m;
        register();
        selectingListModel.setProof(mediator.getSelectedProof());
    }

    public void updateUI() {
        super.updateUI();
        Font myFont = UIManager.getFont(Config.KEY_FONT_GOAL_LIST_VIEW);
        if (myFont != null) {
            setFont(myFont);
        } else {
            LOGGER.debug("goallist: Warning: Use standard font. Could not find font: {}",
                Config.KEY_FONT_GOAL_LIST_VIEW);
        }
    }

    private void register() {
        mediator().addKeYSelectionListener(selectionListener);
        // This method delegates the request only to the UserInterfaceControl
        // which implements the functionality.
        // No functionality is allowed in this method body!
        mediator().getUI().getProofControl().addAutoModeListener(interactiveListener);
        mediator().addGUIListener(guiListener);
    }

    private void unregister() {
        if (mediator() != null) {
            mediator().removeKeYSelectionListener(selectionListener);
            // This method delegates the request only to the UserInterfaceControl
            // which implements the functionality.
            // No functionality is allowed in this method body!
            mediator().getUI().getProofControl().removeAutoModeListener(interactiveListener);
            mediator().removeGUIListener(guiListener);
        }
    }

    public void removeNotify() { // not used?
        // unregister();
        // super.removeNotify();
    }

    private KeYMediator mediator() {
        return mediator;
    }

    private void goalChosen() {
        Goal goal = getSelectedValue();
        if (goal != null) {
            mediator().goalChosen(goal);
        }
    }

    /**
     * overrides setVisible from JFrame takes care that the view item is in the right state
     */
    public void setVisible(boolean b) { // ???
        super.setVisible(b);
    }

    private void selectSelectedGoal() {
        // otherwise it can happen that after removing list entries a wrong row
        // is selected
        clearSelection();

        if (mediator() != null) {
            try {
                final Goal selGoal = mediator().getSelectedGoal();
                if (selGoal != null) {
                    setSelectedValue(selGoal, true);
                }
            } catch (IllegalStateException e) {
                // this exception occurs if no proof is loaded
                // do nothing
                LOGGER.debug("GoalList: No proof loaded.");
            }
        }

        validate();
    }

    private String seqToString(Sequent seq) {
        String res = seqToString.get(seq);
        if (res == null) {
            LogicPrinter sp =
                LogicPrinter.purePrinter(mediator().getNotationInfo(), mediator().getServices());
            sp.printSequent(seq);
            res = sp.result().replace('\n', ' ');
            res = res.substring(0, Math.min(MAX_DISPLAYED_SEQUENT_LENGTH, res.length()));

            seqToString.put(seq, res);
        }
        return res;
    }

    private static class GoalListModel extends AbstractListModel<Goal> {
        private static final long serialVersionUID = 3754243473284250930L;
        /**
         * listens to the proof
         */
        private final ProofTreeListener proofTreeListener = new GoalListProofTreeListener();
        /**
         * the proof the model belongs to
         */
        private Proof proof;
        /**
         *
         */
        private final List<Goal> goals;
        /**
         * is used to indicate if the model has to be updated
         */
        private boolean attentive;

        GoalListModel() {
            goals = new ArrayList<>(10);
        }

        /**
         * the proof this view belongs to has changed
         */
        private void setProof(Proof p) {
            clear();
            if (proof != null) {
                proof.removeProofTreeListener(proofTreeListener);
            }
            proof = p;
            if (proof != null) {
                proof.addProofTreeListener(proofTreeListener);
                add(proof.openGoals());
            }
            attentive = true;
        }

        /**
         * returns true if the model respond to changes in the proof immediately
         */
        public boolean isAttentive() {
            return attentive;
        }

        /**
         * Sets whether this object should respond to changes in the the proof immediately.
         */
        private void setAttentive(boolean b) {
            if ((b != attentive) && (proof != null) && !proof.isDisposed()) {
                if (b) {
                    proof.addProofTreeListener(proofTreeListener);
                    clear();
                    add(proof.openGoals());
                } else {
                    proof.removeProofTreeListener(proofTreeListener);
                }
            }
            attentive = b;
        }

        public void add(ImmutableList<Goal> g) {
            if (!g.isEmpty()) {
                for (Goal aG : g) {
                    goals.add(aG);
                }
                fireIntervalAdded(this, goals.size() - g.size(), goals.size() - 1);
            }
        }

        public void remove(Goal g) {
            int index = goals.indexOf(g);
            if (index > -1) {
                goals.remove(g);
                fireIntervalRemoved(this, index, index);
            }
        }

        public void clear() {
            int size = goals.size();
            if (size > 0) {
                goals.clear();
                fireIntervalRemoved(this, 0, size - 1);
            }
        }

        public int getSize() {
            return goals.size();
        }

        public Goal getElementAt(int i) {
            return goals.get(i);
        }

        class GoalListProofTreeListener implements ProofTreeListener, java.io.Serializable {

            private static final long serialVersionUID = 3090011700136463120L;

            private boolean pruningInProcess;

            /*
             * (non-Javadoc)
             *
             * @see de.uka.ilkd.key.proof.ProofTreeListener#proofExpanded(de.uka.
             * ilkd.key.proof.ProofTreeEvent)
             */
            public void proofExpanded(ProofTreeEvent e) {
                // nothing, this is not important for the list of goals
            }

            /**
             * invoked if all goals of the proof are closed
             */
            public void proofClosed(ProofTreeEvent e) {
                setAttentive(true);
                clear();
            }

            public void proofIsBeingPruned(ProofTreeEvent e) {
                pruningInProcess = true;
            }

            /**
             * The proof tree has been pruned under the node mentioned in the ProofTreeEvent. In
             * other words, that node should no longer have any children now. Any nodes that were
             * not descendants of that node are unaffected.
             */
            public void proofPruned(ProofTreeEvent e) {
                clear();
                add(e.getSource().openGoals());
                pruningInProcess = false;
            }

            /**
             * invoked if the list of goals changed (goals were added, removed etc.
             */
            public void proofGoalRemoved(ProofTreeEvent e) {
                if (pruningInProcess) {
                    return;
                }
                remove(e.getGoal());
            }

            /**
             * invoked if the current goal of the proof changed
             */
            public void proofGoalsAdded(ProofTreeEvent e) {
                if (pruningInProcess) {
                    return;
                }
                add(e.getGoals());
            }

            /**
             * invoked if the current goal of the proof changed
             */
            public void proofGoalsChanged(ProofTreeEvent e) {
                if (pruningInProcess) {
                    return;
                }
                clear();
                add(e.getGoals());
            }

            public void proofStructureChanged(ProofTreeEvent e) {
                if (pruningInProcess) {
                    return;
                }
                clear();
                add(e.getSource().openGoals());
            }

            @Override
            public void notesChanged(ProofTreeEvent e) {
            }
        }
    }

    /**
     * This action enables or disables a selected goal.
     *
     * @author Richard Bubel
     */
    private final class DisableSingleGoal extends DisableGoal {

        /**
         *
         */
        private static final long serialVersionUID = -2035187175105625072L;

        DisableSingleGoal() {
            if (getSelectedValue() != null) {
                final Goal g = getSelectedValue();
                putValue(NAME, g.isAutomatic() ? "Interactive Goal" : "Automatic Goal");
                putValue(SHORT_DESCRIPTION,
                    g.isAutomatic()
                            ? "No automatic rules "
                                + "will be applied when goal is set to interactive."
                            : "Re-enable automatic rule application for this goal.");
                putValue(SMALL_ICON,
                    g.isAutomatic() ? KEY_HOLE_DISABLED_PULL_DOWN_MENU : KEY_HOLE_PULL_DOWN_MENU);
                enableGoals = !g.isAutomatic();
                setEnabled(true);
            } else {
                setEnabled(false);
            }
        }

        /*
         * return singleton list if selectedObject is a goal, an empty list otherwise.
         */
        @Override
        public Iterable<Goal> getGoalList() {
            final Goal selectedObject = getSelectedValue();
            final ArrayList<Goal> selectedGoals = new ArrayList<>();

            if (selectedObject != null) {
                selectedGoals.add(selectedObject);
            }

            return selectedGoals;
        }

        public void actionPerformed(ActionEvent e) {
            super.actionPerformed(e);
            updateUI();
        }

    }

    /**
     * This action dis-/enables all goals except the chosen one.
     *
     * @author Richard Bubel
     */
    private final class DisableOtherGoals extends DisableGoal {

        /**
         *
         */
        private static final long serialVersionUID = 4077876260098617901L;

        DisableOtherGoals() {
            if (getSelectedValue() != null) {
                final Goal g = getSelectedValue();
                putValue(NAME,
                    g.isAutomatic() ? "Set Other Goals Interactive" : "Set Other Goals Automatic");
                putValue(SHORT_DESCRIPTION,
                    g.isAutomatic() ? "No automatic rules " + "will be applied on all other goals."
                            : "Re-enable automatic rule application for other goals.");
                putValue(SMALL_ICON,
                    g.isAutomatic() ? KEY_HOLE_DISABLED_PULL_DOWN_MENU : KEY_HOLE_PULL_DOWN_MENU);
                enableGoals = !g.isAutomatic();

                setEnabled(getModel().getSize() > 1);
            } else {
                setEnabled(false);
            }
        }

        /*
         * return all goals that are not the current goal (=selected value)
         */
        @Override
        public Iterable<Goal> getGoalList() {
            final Object selectedObject = getSelectedValue();
            final List<Goal> selectedGoals = new ArrayList<>();

            for (int i = 0, sz = getModel().getSize(); i < sz; i++) {
                final Goal o = getModel().getElementAt(i);
                if (o != null && o != selectedObject) {
                    selectedGoals.add(o);
                }
            }
            return selectedGoals;
        }

        public void actionPerformed(ActionEvent e) {
            super.actionPerformed(e);
            updateUI();
        }
    }

    /**
     * choose goal as soon as selected
     */
    public class GoalListSelectionListern implements ListSelectionListener {

        public void valueChanged(ListSelectionEvent e) {
            final int firstIndex = e.getFirstIndex();
            if (firstIndex >= 0 && firstIndex < GoalList.this.getModel().getSize()) {
                if (mediator.getSelectedGoal() != GoalList.this.getSelectedValue()) {
                    goalChosen();
                }
            }
        }
    }

    private class GoalListGUIListener implements GUIListener, java.io.Serializable {
        /**
         *
         */
        private static final long serialVersionUID = -1826501525753975124L;

        /**
         * invoked if a frame that wants modal access is opened
         */
        public void modalDialogOpened(EventObject e) {
            setEnabled(false);
        }

        /**
         * invoked if a frame that wants modal access is closed
         */
        public void modalDialogClosed(EventObject e) {
            setEnabled(true);
        }

        public void shutDown(EventObject e) {
        }

    }

    private class GoalListSelectionListener implements KeYSelectionListener {

        /**
         * focused node has changed
         */
        public void selectedNodeChanged(KeYSelectionEvent e) {
            selectSelectedGoal();
        }

        /**
         * the selected proof has changed (e.g. a new proof has been loaded)
         */
        public void selectedProofChanged(KeYSelectionEvent e) {
            LOGGER.debug("GoalList: initialize with new proof");
            selectingListModel.setProof(e.getSource().getSelectedProof());
            validate();
        }
    }

    private class GoalListInteractiveListener implements AutoModeListener {

        /**
         * invoked if automatic execution of heuristics has started
         */
        public void autoModeStarted(ProofEvent e) {
            if (goalListModel.isAttentive()) {
                mediator().removeKeYSelectionListener(selectionListener);
            }
            goalListModel.setAttentive(false);
        }

        /**
         * invoked if automatic execution of heuristics has stopped
         */
        public void autoModeStopped(ProofEvent e) {
            if (!goalListModel.isAttentive()) {
                mediator().addKeYSelectionListener(selectionListener);
            }
            goalListModel.setAttentive(true);
        }

    }

    /**
     * Decorate <code>GoalListModel</code> with a filter that hides certain goals. This is currently
     * used to prevent the display of goals that appear closed for the present user constraint.
     */
    private class SelectingGoalListModel extends AbstractListModel<Goal> {

        /**
         *
         */
        private static final long serialVersionUID = 7395134147866131926L;
        private final GoalListModel delegate;
        /**
         * List of <code>Integer</code> objects that determine the (strictly monotonic) mapping of
         * the row indexes of this model to the rows of the delegate model
         */
        private final ArrayList<Integer> entries = new ArrayList<>(10);
        private final DelegateListener delegateListener = new DelegateListener();
        /**
         * The last known size of the delegate model. This is used to recognise addition or removal
         * of rows
         */
        private int delegateSize;
        private Proof proof = null;

        public SelectingGoalListModel(GoalListModel delegate) {
            this.delegate = delegate;
        }

        public int getSize() {
            return entries.size();
        }

        public Goal getElementAt(int i) {
            if (i < 0 || i >= getSize()) {
                return null;
            }
            return delegate.getElementAt(getDelegateIndex(i));
        }

        private int getDelegateIndex(int i) {
            return entries.get(i);
        }

        /**
         * the proof this view belongs to has changed; this also updates the delegate model
         */
        protected void setProof(Proof p) {
            delegate.removeListDataListener(delegateListener);

            proof = p;

            delegate.setProof(p);
            setup();

            delegate.addListDataListener(delegateListener);
        }

        private boolean isHiddenGoal(final Goal goal) {
            return proof != null
                    && /*
                        * that afterwards should always be false as goals exist only for open nodes
                        */goal.node().isClosed();
        }

        private void setup() {
            entries.clear();
            selectFromInterval(0, delegate.getSize());
            updateDelegateSize();
            fireContentsChanged(this, 0, getSize() - 1);
            selectSelectedGoal(); // this should rather be done by modifying the
            // SelectionModel
        }

        /**
         * Determine the visible goals of a certain interval [delegateBegin, delegateEnd) of the
         * delegate model and create the respective entries of the selection mapping
         *
         * @return the first position of the mapping after the added parts
         */
        private int selectFromInterval(int delegateBegin, int delegateEnd) {
            // defensive
            delegateEnd = Math.min(delegateEnd, delegate.getSize());

            int ind = delegatePosToMappingPos(delegateBegin);

            for (int i = delegateBegin; i < delegateEnd; ++i) {
                final Goal goal = delegate.getElementAt(i);
                if (!isHiddenGoal(goal)) {
                    entries.add(ind++, i);
                }
            }

            return ind;
        }

        /**
         * Remove the parts of the entry mapping for a certain interval [delegateBegin, delegateEnd)
         * of the delegate model
         *
         * @return the first position of the mapping after the removed parts
         */
        private int removeInterval(int delegateBegin, int delegateEnd) {
            final int ind = delegatePosToMappingPos(delegateBegin);

            while (ind != entries.size() && getDelegateIndex(ind) < delegateEnd) {
                entries.remove(ind);
            }

            return ind;
        }

        private int delegatePosToMappingPos(int delegateIndex) {
            // Inefficient, could be implemented using binary search (is there
            // an usable algorithm for this purpose in the Java library?)

            for (int res = 0; res != entries.size(); ++res) {
                if (getDelegateIndex(res) >= delegateIndex) {
                    return res;
                }
            }
            return entries.size();
        }

        /**
         * Shift values of the entries [begin, getSize()) of the selection mapping by the given
         * amount
         */
        private void shiftTail(int begin, int amount) {
            for (; begin != entries.size(); ++begin) {
                entries.set(begin, getDelegateIndex(begin) + amount);
            }
        }

        private int delegateSizeChange() {
            return delegate.getSize() - delegateSize;
        }

        private void updateDelegateSize() {
            delegateSize = delegate.getSize();
        }

        private class DelegateListener implements ListDataListener {
            private int delegateBegin(ListDataEvent e) {
                return e.getIndex0();
            }

            private int delegateEnd(ListDataEvent e) {
                return e.getIndex1() + 1; // we are calculating with right-open
                // intervals
            }

            public void contentsChanged(ListDataEvent e) {
                // this method is currently not used by the delegate and thus
                // not sufficiently tested

                final int oldDelegateEnd = delegateEnd(e) - delegateSizeChange();
                final int begin = removeInterval(delegateBegin(e), oldDelegateEnd);

                shiftTail(begin, delegateSizeChange());

                final int end = selectFromInterval(delegateBegin(e), delegateEnd(e));

                updateDelegateSize();

                final int changeBegin = begin;
                final int changeEnd = end - 1;
                if (changeEnd >= changeBegin) {
                    fireContentsChanged(this, changeBegin, changeEnd);
                }
            }

            public void intervalAdded(ListDataEvent e) {
                final int oldSize = entries.size();
                final int end = selectFromInterval(delegateBegin(e), delegateEnd(e));
                shiftTail(end, delegateSizeChange());

                updateDelegateSize();

                final int addBegin = end - (entries.size() - oldSize);
                final int addEnd = end - 1;
                if (addEnd >= addBegin) {
                    fireIntervalAdded(this, addBegin, addEnd);
                }
            }

            public void intervalRemoved(ListDataEvent e) {
                final int oldSize = entries.size();
                final int begin = removeInterval(delegateBegin(e), delegateEnd(e));
                shiftTail(begin, delegateSizeChange());

                updateDelegateSize();

                final int remBegin = begin;
                final int remEnd = begin + (oldSize - entries.size()) - 1;
                if (remEnd >= remBegin) {
                    fireIntervalRemoved(this, remBegin, remEnd);
                }
            }
        }

    }

    private class IconCellRenderer extends DefaultListCellRenderer implements java.io.Serializable {

        /**
         *
         */
        private static final long serialVersionUID = -8178991338906184819L;

        public IconCellRenderer() {
            GoalList.this.setToolTipText("GOAL");
        }

        public Component getListCellRendererComponent(JList<?> list, Object value, // value
                // to
                // display
                int index, // cell index
                boolean isSelected, // is the cell selected
                boolean cellHasFocus) // the list and the cell have the focus
        {
            String valueStr;
            Color col = Color.black;

            final Icon statusIcon;

            if (value instanceof Goal) {
                final Sequent seq = ((Goal) value).sequent();
                // (DS) Also add the serial of the corresponding node to the
                // printed String for better transparency and quicker
                // access to features like visual node diff.
                valueStr = "(#" + ((Goal) value).node().serialNr() + ") " + seqToString(seq);

                statusIcon = ((Goal) value).isLinked() ? linkedGoalIcon
                        : ((Goal) value).isAutomatic() ? keyIcon : disabledGoalIcon;
            } else {
                valueStr = String.valueOf(value);
                statusIcon = keyIcon;
            }

            DefaultListCellRenderer sup =
                (DefaultListCellRenderer) super.getListCellRendererComponent(list, valueStr, index,
                    isSelected, cellHasFocus);

            sup.setIcon(statusIcon);

            // set color according to closure status
            sup.setForeground(col);

            return sup;
        }
    }
}
