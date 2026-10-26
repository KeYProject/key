/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.*;
import java.util.List;
import java.util.stream.Collectors;
import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.docking.DockingHelper;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.ui.MediatorProofControl;

import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.action.CDropDownButton;
import net.miginfocom.layout.CC;
import net.miginfocom.swing.MigLayout;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * TODO Add documentation!
 *
 * @author Alexander Weigl
 * @version 1 (28.05.19)
 */
@KeYGuiExtension.Info(name = "Keyboard Taclet Control",
    description = "This extension control over the application of taclets via the keyboard.",
    optional = true)
@NullMarked
public class KeyboardTacletExtension implements KeYGuiExtension, KeYGuiExtension.LeftPanel {
    /**
     * The panel is bound by {@link #getPanels(MainWindow, KeYMediator)} after the selection
     * listener is registered; before that it is {@code null}.
     */
    private @Nullable KeyboardTacletPanel panel;

    @Override
    public @NonNull Collection<TabPanel> getPanels(@NonNull MainWindow window,
            @NonNull KeYMediator mediator) {
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
                KeyboardTacletPanel currentPanel = panel;
                if (currentPanel != null) {
                    currentPanel.setGoal(mediator.getSelectedGoal());
                }
            }
        });

        /*
         * window.currentGoalView.setFocusable(true); window.currentGoalView.addKeyListener(new
         * KeyAdapter() {
         *
         * @Override public void keyTyped(KeyEvent e) { panel.processKeyPressed(e); }
         *
         * @Override public void keyPressed(KeyEvent e) { } });
         */

        panel = new KeyboardTacletPanel(window);
        return Collections.singleton(panel);
    }
}


// @SuppressWarnings("WeakerAccess")
@NullMarked
class KeyboardTacletPanel extends JPanel implements TabPanel {
    private static final String PROP_MODEL = "taclets";
    private static final Logger LOGGER = LoggerFactory.getLogger(KeyboardTacletPanel.class);
    private final Services services;
    private final JTextField txtInput = new JTextField();
    private final ActivateAction actionActivate = new ActivateAction();
    private final FilterMouseAction actionFilterUsingMouse = new FilterMouseAction();
    private final DirectModeAction actionDirectMode = new DirectModeAction();
    private final OnlyCompleteTacletsAction actionOnlyCompleteTaclets =
        new OnlyCompleteTacletsAction();
    private final MainWindow mainWindow;
    private @Nullable KeyboardTacletModel model;
    private final Box pCenter = new Box(BoxLayout.Y_AXIS);
    private @Nullable Goal lastGoal;
    /**
     * The listener invokes {@link #updateCurrentPrefix()} and {@link #relayout()} when a
     * property change fires; the checker flags the calls on the receiver while the field is
     * being initialized (EISOP initialization check), suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    private final PropertyChangeListener updateListener = (f) -> {
        updateCurrentPrefix();
        relayout();
    };

    /**
     * The panel configures itself with layout, listener and model calls while the receiver is
     * still under initialization (EISOP initialization check); the effects only take place
     * after construction completes or are deferred into listeners, suppressed with a scoped
     * key. The services object is only queried while a proof is loaded.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public KeyboardTacletPanel(MainWindow mainWindow) {
        this.mainWindow = mainWindow;
        Services services = mainWindow.getMediator().getServices();
        if (services == null) {
            // the panel is only created while a proof is loaded; the previous code crashed
            // with an NPE here
            throw new NullPointerException("No services available.");
        }
        this.services = services;
        // txtInput.setEditable(false);
        setLayout(new BorderLayout());
        JPanel pNorth = new JPanel(new MigLayout("fillX"));
        add(pNorth, BorderLayout.NORTH);
        /*
         * pNorth.add(new JCheckBox(actionActivate)); pNorth.add(new
         * JCheckBox(actionFilterUsingMouse), "wrap"); pNorth.add(new JCheckBox(actionDirectMode),
         * "wrap");
         */
        JLabel lblInput = new JLabel("Input:");
        lblInput.setLabelFor(txtInput);
        pNorth.add(lblInput);
        pNorth.add(txtInput, new CC().growX(1000));

        txtInput.addActionListener(e -> applyCurrentTaclet());
        txtInput.getDocument().addDocumentListener(new DocumentListener() {
            @Override
            public void insertUpdate(DocumentEvent e) {
                checkForApplicability();
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                checkForApplicability();
            }

            @Override
            public void changedUpdate(DocumentEvent e) {
                checkForApplicability();
            }
        });

        mainWindow.getCurrentGoalView().addPropertyChangeListener(
            SequentView.PROP_LAST_MOUSE_POSITION,
            e -> {
                if (actionFilterUsingMouse.isSelected()) {
                    buildModel();
                }
            });

        pCenter.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        add(new JScrollPane(pCenter));
        addPropertyChangeListener(PROP_MODEL, (e) -> {
            if (e.getOldValue() != null) {
                ((KeyboardTacletModel) e.getOldValue())
                        .removePropertyChangeListener(updateListener);
            }
            ((KeyboardTacletModel) e.getNewValue()).addPropertyChangeListener(updateListener);
            updateListener.propertyChange(e);
        });
    }

    private void checkForApplicability() {
        KeyboardTacletModel currentModel = model;
        if (currentModel != null) {
            currentModel.setCurrentPrefix(txtInput.getText());
            if (isDirectMode()) {
                Optional<RuleApp> app = currentModel.getSelectedTacletsApp();
                app.ifPresent(this::applyRule);
            }
        }
    }

    private void applyCurrentTaclet() {
        if (model != null) {
            Optional<RuleApp> app = model.getFirstMatchingTacletApp();
            app.ifPresent(this::applyRule);
            LOGGER.debug("selected taclet applied");
        }
    }

    private void applyRule(RuleApp ruleApp) {
        MediatorProofControl pc = mainWindow.getMediator().getUI().getProofControl();
        Goal goal = lastGoal;
        if (goal == null) {
            // a rule can only be applied while a goal is selected; the previous code crashed
            // with an NPE here
            throw new NullPointerException("No goal selected for the rule application.");
        }
        if (!ruleApp.complete()) {
            try {
                TacletApp tacletApp = (TacletApp) ruleApp;
                ImmutableSet<TacletApp> seq = ImmutableSet.singleton(tacletApp);
                pc.selectedTaclet(seq, goal);
            } catch (ClassCastException ignored) {

            }
        } else {
            pc.applyInteractive(ruleApp, goal);
        }
        mainWindow.setStatusLine("Taclet applied!");
        SwingUtilities.invokeLater(() -> txtInput.setText(""));
    }

    @Override
    public Collection<CAction> getTitleCActions() {
        CDropDownButton btnOptions =
            new CDropDownButton("Options", IconFontSwing.buildIcon(FontAwesomeSolid.COGS, 12));
        btnOptions.add(DockingHelper.translateAction(actionActivate));
        btnOptions.addSeparator();
        btnOptions.add(DockingHelper.translateAction(actionDirectMode));
        btnOptions.add(DockingHelper.translateAction(actionFilterUsingMouse));
        btnOptions.add(DockingHelper.translateAction(actionOnlyCompleteTaclets));
        return Collections.singleton(btnOptions);
    }

    private void updateCurrentPrefix() {
        // txtInput.setText(model.getCurrentPrefix() + " " + model.getCurrentPos());
    }

    /**
     * rebuilds the layout, based on the current model.
     */
    private void relayout() {
        pCenter.removeAll();
        KeyboardTacletModel currentModel = model;
        if (currentModel == null || !actionActivate.isSelected()) {
            return;
        }

        Collection<String> names = currentModel.getPrefixTable().keySet();
        for (String prefix : names) {
            if (!prefix.startsWith(currentModel.getCurrentPrefix())) {
                continue;
            }
            Box box = new Box(BoxLayout.X_AXIS);
            String name = currentModel.getPrefixTable().get(prefix);
            if (name == null) {
                continue;
            }
            int pLength = prefix.length();
            JLabel lblName = new JLabel(
                String.format("<html><u>%s</u>%s</html>", prefix, name.substring(pLength)));
            box.add(lblName);

            int i = 0;
            List<RuleApp> apps = currentModel.getTaclets().get(name);
            if (apps != null) {
                for (RuleApp tacletApp : apps) {
                    box.add(new JLabel(String.valueOf(++i)));// new JLabel(tacletApp.toString()));
                }
            }
            pCenter.add(box);
        }
        pCenter.invalidate();
        pCenter.invalidate();
        pCenter.repaint();
        pCenter.repaint();
        pCenter.repaint();
    }

    public @Nullable KeyboardTacletModel getModel() {
        return model;
    }

    public void setModel(KeyboardTacletModel model) {
        KeyboardTacletModel old = this.model;
        this.model = model;
        firePropertyChange(PROP_MODEL, old, model);
    }

    @Override
    public String getTitle() {
        return "Active Taclets";
    }

    @Override
    public JComponent getComponent() {
        return this;
    }

    public void setGoal(@Nullable Goal selectedGoal) {
        if (this.lastGoal != selectedGoal) {
            lastGoal = selectedGoal;
            buildModel();
        }
    }

    private void buildModel() {
        if (!isActive()) {
            pCenter.removeAll();
            pCenter.add(new JLabel("Not activated."));
            return;
        }

        Goal goal = lastGoal;
        if (goal == null) {
            pCenter.removeAll();
            pCenter.add(new JLabel("Could not get the current goal"));
            pCenter.add(new JLabel("Is a proof loaded?"));
            return;
        }

        long time = System.currentTimeMillis();
        List<RuleApp> taclets = new LinkedList<>();
        PosInSequent pos = mainWindow.getCurrentGoalView().getLastPosInSequent();

        if (actionFilterUsingMouse.isSelected() && pos == null) {
            pCenter.add(
                new JLabel("<html><b>Warning:</b> No last mouse position found in the sequent."));
        }

        if (actionFilterUsingMouse.isSelected() && pos != null) {
            TacletFilter filter = new TacletFilter() {
                @Override
                protected boolean filter(Taclet taclet) {
                    return true;
                }
            };
            try {
                PosInOccurrence pio = pos.getPosInOccurrence();
                if (pio != null) {
                    ImmutableList<NoPosTacletApp> t =
                        goal.ruleAppIndex().getFindTaclet(filter, pio);
                    t.forEach(taclets::add);
                }
            } catch (NullPointerException e) {
                LOGGER.debug("NPE", e);
            }
        } else {
            taclets = goal.getAllBuiltInRuleApps();
            taclets.addAll(goal.getAllTacletApps(services));
        }
        LOGGER.debug("Found {} taclets\n", taclets.size());

        if (actionOnlyCompleteTaclets.isSelected()) {
            taclets = taclets.stream().filter(RuleApp::complete)
                    .collect(Collectors.toList());
        }

        KeyboardTacletModel newModel = new KeyboardTacletModel(taclets);
        setModel(newModel);
        LOGGER.debug("Took: {} ms", System.currentTimeMillis() - time);
    }

    public boolean isActive() {
        return actionActivate.isSelected();
    }

    public boolean isDirectMode() {
        return actionDirectMode.isSelected();
    }

    private class ActivateAction extends KeyAction {
        /**
         * The action configures itself with {@code setName}/{@code setSelected} while the
         * receiver is still under initialization (EISOP initialization check), suppressed with
         * a scoped key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        public ActivateAction() {
            setName("Active");
            setSelected(false);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            buildModel();
        }
    }

    private class FilterMouseAction extends KeyAction {

        /**
         * The action configures itself with {@code setSelected}/{@code setName} while the
         * receiver is still under initialization (EISOP initialization check), suppressed with
         * a scoped key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        public FilterMouseAction() {
            setSelected(true);
            setName("Filter taclets by mouse position");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            buildModel();
        }
    }

    private static class DirectModeAction extends KeyAction {
        /**
         * The action configures itself with {@code setName}/{@code setSelected} while the
         * receiver is still under initialization (EISOP initialization check), suppressed with
         * a scoped key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        public DirectModeAction() {
            setName("Apply directly on unique match.");
            setSelected(true);
        }

        @Override
        public void actionPerformed(ActionEvent e) {

        }
    }

    private class OnlyCompleteTacletsAction extends KeyAction {
        /**
         * The action configures itself with {@code setName}/{@code setSelected} while the
         * receiver is still under initialization (EISOP initialization check), suppressed with
         * a scoped key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        public OnlyCompleteTacletsAction() {
            setName("Show only completed taclets");
            setSelected(false);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            buildModel();
        }
    }
}


/**
 *
 */
@SuppressWarnings("WeakerAccess")
@NullMarked
class KeyboardTacletModel {
    public static final String PROP_CURRENT_PREFIX = "currentPrefix";
    public static final String PROP_CURRENT_POS = "currentPos";
    private final Map<String, List<RuleApp>> taclets;
    private final Map<String, String> prefixTable;
    /**
     * The support object is constructed with the receiver as its source while the receiver is
     * still under initialization (EISOP initialization check); the source reference is only
     * used to fire later events, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:assignment.type.incompatible")
    private final PropertyChangeSupport propertyChangeSupport = new PropertyChangeSupport(this);

    private String currentPrefix;
    private int currentPos;

    /**
     * The constructor copies the taclets, resets the prefix/position state via
     * {@code reset()} and registers itself with a {@code PropertyChangeSupport} while the
     * receiver is still under initialization (EISOP initialization check); the effects only
     * take place after construction completes, suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:initialization.fields.uninitialized",
        "nullness:method.invocation.invalid", "nullness:assignment.type.incompatible" })
    KeyboardTacletModel(List<RuleApp> taclets) {
        reset();
        this.taclets = new HashMap<>();
        List<String> seq = new ArrayList<>(taclets.size());
        for (RuleApp t : taclets) {
            String n = t.rule().name().toString();
            seq.add(n);
            List<RuleApp> appSeq =
                this.taclets.computeIfAbsent(n, it -> (new ArrayList<>(5)));
            appSeq.add(t);
        }

        prefixTable = buildPrefixTable(seq);
    }

    static int getClashFreePrefix(String unique, Collection<String> strings) {
        return strings.stream().filter(it -> !it.equals(unique))
                .mapToInt(c -> getPrefixLength(unique, c)).max().orElse(0);
    }

    static int getPrefixLength(String a, String b) {
        int i = 0;
        for (; i < Math.min(a.length(), b.length()) && (a.charAt(i) == b.charAt(i)
                || !charValid(a.charAt(i)) || !charValid(b.charAt(i))); i++) {
            // empty
        }
        return i;
    }

    static Map<String, String> buildPrefixTable(List<String> seq) {
        Map<String, String> table = new HashMap<>();
        for (String name : seq) {
            int prefixL = getClashFreePrefix(name, seq);
            table.put(name.substring(0, Math.min(prefixL + 1, name.length())), name);
        }
        return table;
    }

    static boolean charValid(char c) {
        return true; // return ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z');
    }

    public void addPropertyChangeListener(PropertyChangeListener listener) {
        propertyChangeSupport.addPropertyChangeListener(listener);
    }

    public void removePropertyChangeListener(PropertyChangeListener listener) {
        propertyChangeSupport.removePropertyChangeListener(listener);
    }

    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        propertyChangeSupport.addPropertyChangeListener(propertyName, listener);
    }

    public void processChar(char c) {
        switch (c) {
            case '\u001B' -> // escape
                reset();
            case '\b' -> {
                if (currentPrefix.length() <= 1) {
                    setCurrentPrefix("");
                } else {
                    setCurrentPrefix(currentPrefix.substring(0, currentPrefix.length() - 1));
                }
            }
            default -> {
                if ('0' <= c && c <= '9') {
                    setCurrentPos(c - '0');
                }
                if (charValid(c)) {
                    setCurrentPrefix(currentPrefix + c);
                }
            }
        }
    }

    public int getCurrentPos() {
        return currentPos;
    }

    public void setCurrentPos(int currentPos) {
        int old = this.currentPos;
        this.currentPos = currentPos;
        propertyChangeSupport.firePropertyChange(PROP_CURRENT_POS, old, currentPos);
    }

    private void reset() {
        setCurrentPrefix("");
        setCurrentPos(-1);
    }

    public Optional<RuleApp> getSelectedTacletsApp() {
        String prefix = prefixTable.get(currentPrefix);
        if (prefix == null) {
            return Optional.empty();
        }
        List<RuleApp> t = taclets.get(prefix);
        if (t != null && (t.size() == 1 || (currentPos >= 0 && currentPos <= taclets.size()))) {
            return Optional.of(t.get(Math.max(0, currentPos)));
        }
        return Optional.empty();
    }

    public Optional<RuleApp> getFirstMatchingTacletApp() {
        for (String prefix : getPrefixTable().keySet()) {
            if (prefix.startsWith(currentPrefix)) {
                String tacletName = prefixTable.get(prefix);
                if (tacletName == null) {
                    return Optional.empty();
                }
                List<RuleApp> apps = taclets.get(tacletName);
                if (apps == null || apps.isEmpty()) {
                    return Optional.empty();
                }
                return Optional.of(apps.get(0));
            }
        }
        return Optional.empty();
    }

    public Map<String, String> getPrefixTable() {
        return prefixTable;
    }

    public String getCurrentPrefix() {
        return currentPrefix;
    }

    public void setCurrentPrefix(String currentPrefix) {
        String old = this.currentPrefix;
        this.currentPrefix = currentPrefix;
        propertyChangeSupport.firePropertyChange(PROP_CURRENT_PREFIX, old, currentPrefix);
    }

    public Collection<String> getTacletNames() {
        return prefixTable.values().stream().sorted().collect(Collectors.toList());
    }

    public Map<String, List<RuleApp>> getTaclets() {
        return taclets;
    }
}
