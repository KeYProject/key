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
                System.out.println("KeyboardTacletExtension.keyTyped");
                System.out.println("e = [" + e + "]");
            }

            @Override
            public void keyPressed(KeyEvent e) {
                System.out.println("KeyboardTacletExtension.keyPressed");
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
    private KeyboardTacletModel model;
    private Box pCenter = new Box(BoxLayout.Y_AXIS);
    private Goal lastGoal;

    public KeyboardTacletPanel(Services services) {
        this.services = services;
        setLayout(new BorderLayout());
        JPanel pNorth = new JPanel();
        add(pNorth, BorderLayout.NORTH);
        pNorth.add(new JCheckBox(actionActivate));
        pNorth.add(new JCheckBox(actionFilterUsingMouse));
        add(pCenter);
        addPropertyChangeListener(PROP_MODEL, (e) -> relayout());
    }

    /**
     * rebuilds the layout, based on the current model.
     */
    private void relayout() {
        pCenter.removeAll();
        if (model == null || !actionActivate.isSelected()) {
            return;
        }

        Collection<String> names = model.getPrefixTable().keySet();
        for (String prefix : names) {
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
        if (lastGoal != null) return;
        long time = System.currentTimeMillis();
        List<RuleApp> taclets = new LinkedList<>();
        PosInSequent pos = MainWindow.getInstance().currentGoalView.getMousePosInSequent();
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
        KeyboardTacletModel newModel = new KeyboardTacletModel(taclets);
        setModel(newModel);
        System.out.format("Took: %d ms%n", System.currentTimeMillis() - time);
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
}

/**
 *
 */
class KeyboardTacletModel {
    private final Map<String, List<RuleApp>> taclets;
    private final Map<String, String> prefixTable;

    private String currentPrefix;
    private int currentPos;

    KeyboardTacletModel(List<RuleApp> taclets) {
        this.taclets = new HashMap<>();
        List<String> seq = new ArrayList<>(taclets.size());
        for (RuleApp t : taclets) {
            String n = t.rule().name().toString();
            seq.add(n);
            this.taclets.computeIfAbsent(n, it -> (new ArrayList<>(5)));
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

    public void processChar(char c) {
        if (c == '\027') {
            reset();
        } else {
            if ('0' <= c && c <= '9')
                currentPos = c - '0';
            else
                currentPrefix += c;
        }
    }

    private void reset() {
        currentPrefix = "";
        currentPos = -1;
    }

    public Optional<RuleApp> getSelectedTacletsApp() {
        List<RuleApp> t = taclets.get(prefixTable.get(currentPrefix));
        if (t.size() == 1 || (currentPos >= 0 && currentPos <= taclets.size())) {
            return Optional.of(t.get(Math.max(0, currentPos)));
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
        this.currentPrefix = currentPrefix;
    }

    public Collection<String> getTacletNames() {
        return prefixTable.values().stream().sorted().collect(Collectors.toList());
    }

    public Map<String, List<RuleApp>> getTaclets() {
        return taclets;
    }
}

/*class PatriciaNode {
    String value;
    PatriciaNode[] indexes = new PatriciaNode[2 * 26]; // characters in alphabet

    static int getIndex(char c) {
        return c > 'Z' ? c - 'A' : c - 'a';
    }

    static boolean charValid(char c) {
        return ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z');
    }

    static int[] getIndices(String name) {
        char[] c = name.toCharArray();

    }

    PatriciaNode get(String key) {

    }

    PatriciaNode get(String key) {

    }
}*/