package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import org.key_project.util.collection.ImmutableList;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.List;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (28.05.19)
 */
@KeYGuiExtension.Info()
public class KeyboardTacletExtension implements KeYGuiExtension,
        KeYGuiExtension.LeftPanel {
    private KeyboardTacletPanel panel;

    @Override
    public Collection<TabPanel> getPanels(MainWindow window, KeYMediator mediator) {
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                panel.setGoal(mediator.getSelectedGoal());
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {

            }
        });

        window.currentGoalView.setFocusable(true);
        window.currentGoalView.addKeyListener(new KeyAdapter() {
            @Override
            public void keyTyped(KeyEvent e) {
                panel.processKeyPressed(e);
            }

            @Override
            public void keyPressed(KeyEvent e) {
            }
        });

        panel = new KeyboardTacletPanel(window.getMediator().getServices());
        return Collections.singleton(panel);
    }
}

class KeyboardTacletPanel extends JPanel implements TabPanel {
    private static final String PROP_MODEL = "taclets";
    private final Services services;
    private ActivateAction actionActivate = new ActivateAction();
    private FilterMouseAction actionFilterUsingMouse = new FilterMouseAction();
    private DirectModeAction actionDirectMode = new DirectModeAction();

    private KeyboardTacletModel model;
    private Box pCenter = new Box(BoxLayout.Y_AXIS);
    private Goal lastGoal;
    private JLabel txtCurrentPrefix = new JLabel();

    private PropertyChangeListener updateListener = (f) -> {
        updateCurrentPrefix();
        relayout();
    };

    public KeyboardTacletPanel(Services services) {
        this.services = services;
        //txtCurrentPrefix.setEditable(false);
        setLayout(new BorderLayout());
        JPanel pNorth = new JPanel();
        add(pNorth, BorderLayout.NORTH);
        pNorth.add(new JCheckBox(actionActivate));
        pNorth.add(new JCheckBox(actionFilterUsingMouse));
        pNorth.add(new JCheckBox(actionDirectMode));
        add(new JScrollPane(pCenter));
        addPropertyChangeListener(PROP_MODEL, (e) -> {
            if (e.getOldValue() != null)
                ((KeyboardTacletModel) e.getOldValue()).removePropertyChangeListener(updateListener);
            ((KeyboardTacletModel) e.getNewValue()).addPropertyChangeListener(updateListener);
            updateListener.propertyChange(e);
        });
    }

    private void updateCurrentPrefix() {
        txtCurrentPrefix.setText(model.getCurrentPrefix() + " " + model.getCurrentPos());
    }

    /**
     * rebuilds the layout, based on the current model.
     */
    private void relayout() {
        pCenter.removeAll();
        if (model == null || !actionActivate.isSelected()) {
            return;
        }

        Box boxPrefix = new Box(BoxLayout.X_AXIS);
        pCenter.add(boxPrefix);
        boxPrefix.add(new JLabel("Current prefix:"));
        boxPrefix.add(txtCurrentPrefix);

        Collection<String> names = model.getPrefixTable().keySet();
        for (String prefix : names) {
            if (!prefix.startsWith(model.getCurrentPrefix())) {
                continue;
            }
            Box box = new Box(BoxLayout.X_AXIS);
            String name = model.getPrefixTable().get(prefix);
            int pLength = prefix.length();
            JLabel lblName = new JLabel(
                    String.format("<html><u>%s</u>%s</html>",
                            prefix, name.substring(pLength)));
            box.add(lblName);

            for (RuleApp tacletApp : model.getTaclets().get(name)) {
                box.add(new JLabel(tacletApp.toString()));
            }
            pCenter.add(box);
        }
        pCenter.invalidate();
        pCenter.invalidate();
        pCenter.repaint();
        pCenter.repaint();
        pCenter.repaint();
    }

    public KeyboardTacletModel getModel() {
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

    public void setGoal(Goal selectedGoal) {
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

        if (lastGoal == null) {
            pCenter.removeAll();
            pCenter.add(new JLabel("Could not get the current goal"));
            pCenter.add(new JLabel("Is a proof loaded?"));
            return;
        }

        long time = System.currentTimeMillis();
        List<RuleApp> taclets = new LinkedList<>();
        PosInSequent pos = MainWindow.getInstance().currentGoalView.getMousePosInSequent();

        if (actionFilterUsingMouse.isSelected() && pos == null) {
            pCenter.add(new JLabel("<html><b>Warning:</b> No last mouse position found in the sequent."));
        }

        if (actionFilterUsingMouse.isSelected() && pos != null) {
            TacletFilter filter = new TacletFilter() {
                @Override
                protected boolean filter(Taclet taclet) {
                    return true;
                }
            };

            ImmutableList<NoPosTacletApp> t = lastGoal.ruleAppIndex().getFindTaclet(
                    filter, pos.getPosInOccurrence(), services
            );
            t.forEach(taclets::add);
        } else {
            taclets = lastGoal.getAllBuiltInRuleApps();
            taclets.addAll(lastGoal.getAllTacletApps(services));
        }
        System.out.format("Found %d taclets\n", taclets.size());
        KeyboardTacletModel newModel = new KeyboardTacletModel(taclets);
        setModel(newModel);
        System.out.format("Took: %d ms%n", System.currentTimeMillis() - time);
    }

    public boolean isActive() {
        return actionActivate.isSelected();
    }

    public boolean isDirectMode() {
        return actionDirectMode.isSelected();
    }

    public void processKeyPressed(KeyEvent e) {
        if (model != null) {
            model.processChar(e.getKeyChar());
            if (isDirectMode()) {
                Optional<RuleApp> app = model.getSelectedTacletsApp();
                app.ifPresent(ruleApp -> {
                    ruleApp.execute(lastGoal, services);
                    System.out.println("applied");
                });
            }

            if (e.getKeyCode() == KeyEvent.VK_ENTER) {
                Optional<RuleApp> app = model.getFirstMatchingTacletApp();
                app.ifPresent(ruleApp -> ruleApp.execute(lastGoal, services));
                System.out.println("applied");
            }
        }
    }

    public class FilterMouseAction extends KeyAction {

        public FilterMouseAction() {
            setSelected(true);
            setName("Filter taclets by mouse position");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            buildModel();
        }
    }

    private class ActivateAction extends KeyAction {
        public ActivateAction() {
            setName("Active");
            setSelected(false);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            buildModel();
        }
    }

    class DirectModeAction extends KeyAction {
        public DirectModeAction() {
            setName("Apply directly on unique match.");
            setSelected(true);
        }

        @Override
        public void actionPerformed(ActionEvent e) {

        }
    }
}

/**
 *
 */
class KeyboardTacletModel {
    public static final String PROP_CURRENT_PREFIX = "currentPrefix";
    public static final String PROP_CURRENT_POS = "currentPos";
    private final Map<String, List<RuleApp>> taclets;
    private final Map<String, String> prefixTable;
    private PropertyChangeSupport propertyChangeSupport = new PropertyChangeSupport(this);

    private String currentPrefix;
    private int currentPos;

    KeyboardTacletModel(List<RuleApp> taclets) {
        reset();
        this.taclets = new HashMap<>();
        List<String> seq = new ArrayList<>(taclets.size());
        for (RuleApp t : taclets) {
            String n = t.rule().name().toString();
            seq.add(n);
            List<RuleApp> appSeq = this.taclets.computeIfAbsent(n, it -> (new ArrayList<>(5)));
            appSeq.add(t);
        }

        prefixTable = buildPrefixTable(seq);
    }

    static int getClashFreePrefix(String unique, Collection<String> strings) {
        return strings.stream()
                .filter(it -> !it.equals(unique))
                .mapToInt(c -> getPrefixLength(unique, c))
                .max().orElse(0);
    }

    static int getPrefixLength(String a, String b) {
        int i = 0;
        for (; i < Math.min(a.length(), b.length()) &&
                (a.charAt(i) == b.charAt(i) || !charValid(a.charAt(i)) || !charValid(b.charAt(i)))
                ; i++)
            ;
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
        return ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z');
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
            case '\u001B': //escape
                reset();
                break;
            case '\b':
                if (currentPrefix.length() <= 1)
                    setCurrentPrefix("");
                else
                    setCurrentPrefix(currentPrefix.substring(0, currentPrefix.length() - 1));
                break;
            default:
                if ('0' <= c && c <= '9') {
                    setCurrentPos(c - '0');
                }
                if (charValid(c)) {
                    setCurrentPrefix(currentPrefix + c);
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
        List<RuleApp> t = taclets.get(prefixTable.get(currentPrefix));
        if (t != null && t.size() == 1 || (currentPos >= 0 && currentPos <= taclets.size())) {
            assert t != null;
            return Optional.of(t.get(Math.max(0, currentPos)));
        }
        return Optional.empty();
    }

    public Optional<RuleApp> getFirstMatchingTacletApp() {
        for (String prefix : getPrefixTable().keySet()) {
            if (prefix.startsWith(currentPrefix)) {
                String tacletName = prefixTable.get(prefix);
                List<RuleApp> apps = taclets.get(tacletName);
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
