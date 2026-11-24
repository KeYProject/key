/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.beans.PropertyChangeListener;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.geometry.Insets;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextField;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.control.DefaultProofControl;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.docking.DockTitleActionF;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The "Active Taclets" panel of the keyboard-taclet extension, JavaFX port of the package-private
 * {@code KeyboardTacletPanel} of the Swing original
 * (key.ui/src/main/java/de/uka/ilkd/key/gui/KeyboardTacletExtension.java:89-385). The user types
 * a rule-name prefix into the input field (or, on the panel itself, single characters) and the
 * panel lists the applicable taclets whose names start with that prefix, underlining the matched
 * part; a unique match can be applied directly (direct mode), otherwise the number keys select
 * one of the numbered applications.
 * <p>
 * Swing parity notes and KNOWN-SIMPLIFIED decisions of this port (each marked at the site):
 * <ul>
 * <li>The four toggles ({@code ActivateAction}, {@code DirectModeAction},
 * {@code FilterMouseAction}, {@code OnlyCompleteTacletsAction},
 * KeyboardTacletExtension.java:337-384) are Boolean properties rendered as check boxes inside the
 * panel header — the Swing original exposes them as check-style actions in the dock-title
 * {@code CDropDownButton} "Options" (KeyboardTacletExtension.java:199-209), which has no FX
 * drawer counterpart; inline check boxes match the commented-out sketch in the Swing source
 * (KeyboardTacletExtension.java:115-119). The same toggles are additionally exposed as
 * check-style {@link DockTitleActionF}s via {@link #getTitleActions()} for the dock-tab title
 * context menu.</li>
 * <li>The mouse-position seam: the Swing panel observes
 * {@code SequentView.PROP_LAST_MOUSE_POSITION} (KeyboardTacletExtension.java:143-149) and rebuilds
 * on it; the FX seam is {@code SequentViewF.hoveredPosProperty()} (attached in {@link #wire}).
 * Unlike the Swing getter {@code getLastPosInSequent} (SequentView.java:349-356), which returns a
 * toplevel {@code PosInSequent.createSequentPos()} position when the mouse is outside, the FX
 * hover position is {@code null} there — the {@code null} routes into the "no last mouse
 * position" warning plus the all-taclets fallback branch, whereas the Swing toplevel position
 * made {@code getFindTaclet} fail with a {@link NullPointerException} (caught at
 * KeyboardTacletExtension.java:306-312) into an empty taclet list.</li>
 * <li>The {@code Services} are taken from the current goal's proof on every rebuild
 * ({@code lastGoal.proof().getServices()}) — KNOWN-SIMPLIFIED (FIXED-UPSTREAM): the Swing panel
 * captures {@code mainWindow.getMediator().getServices()} once in the constructor
 * (KeyboardTacletExtension.java:110) and reuses it for every rebuild, so a proof swap could leak
 * a stale services instance into {@code getAllTacletApps}.</li>
 * <li>The keyboard feed on the panel content (ESC, backspace, typed characters) mirrors the
 * commented-out Swing sketch that wanted the same on the sequent view
 * (KeyboardTacletExtension.java:73-80); the feed lives on the panel itself here and is skipped
 * when the event targets the input field — the field feeds the model through its text listener
 * like the Swing {@code DocumentListener} (KeyboardTacletExtension.java:126-141).</li>
 * <li>The warning label of {@link #buildModel()} is added and then immediately wiped again by the
 * {@code relayout()} triggered through {@code setModel} — a preserved Swing quirk
 * (KeyboardTacletExtension.java:294-297 added before KeyboardTacletExtension.java:325 fires the
 * model property change).</li>
 * </ul>
 * The panel constructs JavaFX controls, so it is only built lazily by
 * {@link KeyboardTacletExtensionF} once a window exists (toolkit-free provider instantiation).
 */
class KeyboardTacletPanelF extends BorderPane {
    private static final Logger LOGGER = LoggerFactory.getLogger(KeyboardTacletPanelF.class);

    private final TextField txtInput = new TextField();
    // the four toggles as Boolean properties (Swing KeyActions with SELECTED_KEY; the defaults
    // mirror KeyboardTacletExtension.java:337-384: active=false, directMode=true,
    // filterUsingMouse=true, onlyCompleteTaclets=false)
    private final BooleanProperty active = new SimpleBooleanProperty(false);
    private final BooleanProperty directMode = new SimpleBooleanProperty(true);
    private final BooleanProperty filterUsingMouse = new SimpleBooleanProperty(true);
    private final BooleanProperty onlyCompleteTaclets = new SimpleBooleanProperty(false);

    private final @Nullable MainWindowF mainWindow;
    private final @Nullable KeYMediatorF mediator;
    private final VBox pCenter = new VBox();
    private @Nullable KeyboardTacletModelF model;
    private @Nullable Goal lastGoal;
    private final PropertyChangeListener updateListener = f -> {
        updateCurrentPrefix();
        relayout();
    };

    /** the window the hover listener is attached to (idempotent re-wiring in {@link #wire}). */
    private @Nullable MainWindowF hoverWiredWindow;

    KeyboardTacletPanelF(@Nullable MainWindowF mainWindow, @Nullable KeYMediatorF mediator) {
        this.mainWindow = mainWindow;
        this.mediator = mediator;

        // Swing: setLayout(new BorderLayout()) + pNorth (MigLayout "fillX") added NORTH
        // (KeyboardTacletExtension.java:112-114) — the header holds the toggle check boxes
        // (KNOWN-SIMPLIFIED, see class javadoc) and the input row
        setTop(buildNorth());

        // Swing: pCenter (Box Y_AXIS) with empty border 5,5,5,5 inside a JScrollPane at CENTER
        // (KeyboardTacletExtension.java:101, 151-152)
        pCenter.setPadding(new Insets(5));
        ScrollPane scroll = new ScrollPane(pCenter);
        scroll.setFitToWidth(true);
        setCenter(scroll);

        // keyboard feed on the panel content (Swing sketch KeyboardTacletExtension.java:73-80):
        // ESC and backspace and every typed character drive model.processChar, unless the event
        // targets the input field — the field feeds the model through its text listener
        // (checkForApplicability), so the panel feed must neither consume nor double-feed there
        addEventFilter(KeyEvent.KEY_PRESSED, e -> {
            if (e.getTarget() == txtInput) {
                return; // no consume, no double-feed
            }
            if (e.getCode() == KeyCode.ESCAPE) {
                processChar('\u001B');
                e.consume();
            } else if (e.getCode() == KeyCode.BACK_SPACE) {
                processChar('\b');
                e.consume();
            }
        });
        addEventFilter(KeyEvent.KEY_TYPED, e -> {
            if (e.getTarget() == txtInput) {
                return; // no consume, no double-feed
            }
            String characters = e.getCharacter();
            if (characters.isEmpty()) {
                return;
            }
            char c = characters.charAt(0);
            if (c < ' ') {
                // control characters (JavaFX additionally delivers ESC/backspace as KEY_TYPED)
                // are handled by the KEY_PRESSED filter above — skipping avoids a double feed
                return;
            }
            processChar(c);
        });
        // click-to-focus so the panel feed receives the keys after a click on the panel itself
        setFocusTraversable(true);
        addEventFilter(MouseEvent.MOUSE_PRESSED, e -> {
            if (e.getTarget() == this && !isFocused()) {
                requestFocus();
            }
        });
    }

    /**
     * (Re-)wires the window/mediator context. The provider re-wires from {@code StartupF.init}
     * after the window construction (Exploration pattern); the hover listener of the Swing panel
     * (KeyboardTacletExtension.java:143-149) is attached here exactly once, to the first
     * non-{@code null} window.
     */
    void wire(@Nullable MainWindowF window, @Nullable KeYMediatorF mediator) {
        if (window != null && window != hoverWiredWindow) {
            hoverWiredWindow = window;
            window.getSequentView().hoveredPosProperty().addListener((obs, o, n) -> {
                if (filterUsingMouse.get()) {
                    buildModel();
                }
            });
        }
    }

    /**
     * The toggle check boxes and the input row (Swing pNorth, KeyboardTacletExtension.java:113).
     */
    private VBox buildNorth() {
        // KNOWN-SIMPLIFIED: check boxes in the header instead of the Swing dock-title
        // CDropDownButton "Options" (KeyboardTacletExtension.java:199-209); the toggles keep the
        // Swing drop-down order (activate, direct mode, filter by mouse, only complete)
        // KNOWN-SIMPLIFIED: cosmetic 8px gap (Swing had the look&feel's check box insets)
        HBox toggles = new HBox(8, toggle("Active", active, true),
            toggle("Apply directly on unique match.", directMode, false),
            toggle("Filter taclets by mouse position", filterUsingMouse, true),
            toggle("Show only completed taclets", onlyCompleteTaclets, true));

        Label lblInput = new Label("Input:");
        lblInput.setLabelFor(txtInput);
        // KNOWN-SIMPLIFIED: cosmetic 4px gap (Swing had the MigLayout default gap)
        HBox inputRow = new HBox(4, lblInput, txtInput);
        HBox.setHgrow(txtInput, Priority.ALWAYS); // Swing CC().growX(1000)
        return new VBox(toggles, inputRow);
    }

    /**
     * One toggle check box bound to its property. The Swing {@code actionPerformed} of
     * {@code ActivateAction}, {@code FilterMouseAction} and {@code OnlyCompleteTacletsAction}
     * rebuilds the model (KeyboardTacletExtension.java:343-346, 356-359, 380-383);
     * {@code DirectModeAction.actionPerformed} is empty (KeyboardTacletExtension.java:368-371) —
     * a preserved quirk, the flag is read live by {@link #checkForApplicability} and
     * {@link #processChar}.
     */
    private CheckBox toggle(String label, BooleanProperty property, boolean rebuild) {
        CheckBox check = new CheckBox(label);
        check.selectedProperty().bindBidirectional(property);
        if (rebuild) {
            property.addListener((obs, o, n) -> buildModel());
        }
        return check;
    }

    /** Feeds one character into the model and applies a unique match in direct mode. */
    private void processChar(char c) {
        KeyboardTacletModelF m = model;
        if (m == null) {
            return;
        }
        m.processChar(c);
        if (directMode.get()) {
            m.getSelectedTacletsApp().ifPresent(this::applyRule);
        }
    }

    private void checkForApplicability() {
        // Swing KeyboardTacletExtension.java:164-172
        KeyboardTacletModelF m = model;
        if (m != null) {
            m.setCurrentPrefix(txtInput.getText());
            if (isDirectMode()) {
                m.getSelectedTacletsApp().ifPresent(this::applyRule);
            }
        }
    }

    private void applyCurrentTaclet() {
        // Swing KeyboardTacletExtension.java:174-180
        KeyboardTacletModelF m = model;
        if (m != null) {
            m.getFirstMatchingTacletApp().ifPresent(this::applyRule);
            LOGGER.debug("selected taclet applied");
        }
    }

    private void applyRule(RuleApp ruleApp) {
        // Swing KeyboardTacletExtension.java:182-197
        MainWindowF w = mainWindow;
        if (w == null) {
            // panel without a host window (toolkit-free wiring): nothing to apply
            return;
        }
        // Swing: MediatorProofControl pc = mainWindow.getMediator().getUI().getProofControl()
        // (KeyboardTacletExtension.java:183); the FX host returns the same
        // DefaultProofControl directly (WindowUserInterfaceControlF.getProofControl)
        DefaultProofControl pc = w.getUserInterfaceControl().getProofControl();
        if (!ruleApp.complete()) {
            try {
                TacletApp tacletApp = (TacletApp) ruleApp;
                ImmutableSet<TacletApp> seq = ImmutableSet.singleton(tacletApp);
                pc.selectedTaclet(seq, lastGoal);
            } catch (ClassCastException ignored) {
                // Swing parity: only taclet applications can be completed interactively here
            }
        } else {
            pc.applyInteractive(ruleApp, lastGoal);
        }
        w.setStatusLine("Taclet applied!");
        // Swing defers the clearing with SwingUtilities.invokeLater
        // (KeyboardTacletExtension.java:196) so that it runs after the modal taclet-match dialog
        // closed; the FX taclet-match dialog is synchronous as well (FxUtil.runAndWait inside
        // the proof control) and this method already runs on the FX Application Thread, so the
        // direct clearing is the exact equivalent point in time
        txtInput.setText("");
    }

    /**
     * The four toggles as check-style title actions — the hook for the dock-tab title context
     * menu (Swing {@code TabPanel.getTitleCActions}, the "Options" {@code CDropDownButton} with
     * the COGS icon, KeyboardTacletExtension.java:199-209, whose items are check-style
     * bibliothek {@code CCheckBox}es via {@code DockingHelper.createCheckBox},
     * DockingHelper.java:188-223). The FX dock workspace currently renders
     * {@link DockTitleActionF}s as plain menu items ({@code DockWorkspace.createTabContextMenu},
     * DockWorkspace.java:413-432); rendering the {@link DockTitleActionF#selected()} flavour as
     * check menu items is host work (see the KNOWN-SIMPLIFIED ledger). The action flips the
     * toggle, which re-renders the header check box via the bidirectional binding and rebuilds
     * the model.
     */
    public List<DockTitleActionF> getTitleActions() {
        return List.of(
            new DockTitleActionF("Active", active.get(), () -> active.set(!active.get())),
            new DockTitleActionF("Apply directly on unique match.", directMode.get(),
                () -> directMode.set(!directMode.get())),
            new DockTitleActionF("Filter taclets by mouse position", filterUsingMouse.get(),
                () -> filterUsingMouse.set(!filterUsingMouse.get())),
            new DockTitleActionF("Show only completed taclets", onlyCompleteTaclets.get(),
                () -> onlyCompleteTaclets.set(!onlyCompleteTaclets.get())));
    }

    private void updateCurrentPrefix() {
        // txtInput.setText(model.getCurrentPrefix() + " " + model.getCurrentPos());
        // (Swing parity: the body is commented out in the original,
        // KeyboardTacletExtension.java:211-213)
    }

    /**
     * Rebuilds the layout, based on the current model (Swing
     * KeyboardTacletExtension.java:218-247): one row per taclet whose name starts with the
     * current prefix, the matched prefix underlined (Swing {@code <html><u>…</u>…</html>}), the
     * applications numbered.
     */
    private void relayout() {
        pCenter.getChildren().clear();
        KeyboardTacletModelF m = model;
        if (m == null || !active.get()) {
            return;
        }

        Collection<String> names = m.getPrefixTable().keySet();
        for (String prefix : names) {
            if (!prefix.startsWith(m.getCurrentPrefix())) {
                continue;
            }
            HBox box = new HBox();
            String name = m.getPrefixTable().get(prefix);
            assert name != null;
            int pLength = prefix.length();
            // Swing renders "<html><u>prefix</u>rest</html>" in a single label
            // (KeyboardTacletExtension.java:232-234); the underlined prefix and the plain rest
            // are two labels here
            Label lblName = new Label(prefix);
            lblName.setStyle("-fx-underline: true;");
            box.getChildren().add(lblName);
            box.getChildren().add(new Label(name.substring(pLength)));

            List<RuleApp> apps = m.getTaclets().get(name);
            assert apps != null;
            // Swing kept the app label commented out
            // (KeyboardTacletExtension.java:238): // new JLabel(tacletApp.toString())
            int i = 0;
            for (RuleApp tacletApp : apps) {
                box.getChildren().add(new Label(String.valueOf(++i)));
            }
            pCenter.getChildren().add(box);
        }
        // the Swing quirk pCenter.invalidate()x2/repaint()x3
        // (KeyboardTacletExtension.java:242-246) has no FX counterpart: the scene graph
        // invalidates itself
    }

    public @Nullable KeyboardTacletModelF getModel() {
        return model;
    }

    public void setModel(@Nullable KeyboardTacletModelF model) {
        // Swing: firePropertyChange(PROP_MODEL, old, model) observed by the PROP_MODEL listener
        // registered in the constructor (KeyboardTacletExtension.java:153-160) — the
        // listener behaviour is folded into this setter (PropertyChangeSupport only fires for
        // old != new)
        KeyboardTacletModelF old = this.model;
        if (old == model) {
            return;
        }
        this.model = model;
        if (old != null) {
            old.removePropertyChangeListener(updateListener);
        }
        if (model != null) {
            model.addPropertyChangeListener(updateListener);
        }
        updateCurrentPrefix();
        relayout();
    }

    /** @return the tab title (Swing {@code getTitle}, KeyboardTacletExtension.java:259-262) */
    public String getTitle() {
        return "Active Taclets";
    }

    public void setGoal(@Nullable Goal selectedGoal) {
        // Swing KeyboardTacletExtension.java:269-274
        if (this.lastGoal != selectedGoal) {
            lastGoal = selectedGoal;
            buildModel();
        }
    }

    private void buildModel() {
        // Swing KeyboardTacletExtension.java:276-327
        if (!active.get()) {
            pCenter.getChildren().clear();
            pCenter.getChildren().add(new Label("Not activated."));
            return;
        }

        if (lastGoal == null) {
            pCenter.getChildren().clear();
            pCenter.getChildren().add(new Label("Could not get the current goal"));
            pCenter.getChildren().add(new Label("Is a proof loaded?"));
            return;
        }

        long time = System.currentTimeMillis();
        List<RuleApp> taclets = new LinkedList<>();
        // Swing queries mainWindow.getCurrentGoalView().getLastPosInSequent() — a toplevel
        // sequent position when the mouse is outside (SequentView.java:349-356). The FX hover
        // seam (SequentViewF.getHoveredPos) is null instead in that case; see the class javadoc
        MainWindowF w = mainWindow;
        PosInSequent pos = w == null ? null : w.getSequentView().getHoveredPos();

        if (filterUsingMouse.get() && pos == null) {
            // Swing parity quirk: this label is added without clearing pCenter first and is
            // then immediately wiped again by the relayout() triggered through setModel below
            pCenter.getChildren().add(new Label(
                "<html><b>Warning:</b> No last mouse position found in the sequent."));
        }

        if (filterUsingMouse.get() && pos != null) {
            // Swing builds an anonymous all-accepting TacletFilter
            // (KeyboardTacletExtension.java:300-305); TacletFilter.TRUE is that filter
            try {
                ImmutableList<NoPosTacletApp> t = lastGoal.ruleAppIndex()
                        .getFindTaclet(TacletFilter.TRUE, pos.getPosInOccurrence());
                t.forEach(taclets::add);
            } catch (NullPointerException e) {
                LOGGER.debug("NPE", e);
            }
        } else {
            // KNOWN-SIMPLIFIED (FIXED-UPSTREAM): services per goal/proof instead of the
            // once-captured mediator services (see class javadoc)
            Services services = lastGoal.proof().getServices();
            taclets = lastGoal.getAllBuiltInRuleApps();
            taclets.addAll(lastGoal.getAllTacletApps(services));
        }
        LOGGER.debug("Found {} taclets\n", taclets.size());

        if (onlyCompleteTaclets.get()) {
            taclets = taclets.stream().filter(RuleApp::complete).collect(Collectors.toList());
        }

        KeyboardTacletModelF newModel = new KeyboardTacletModelF(taclets);
        setModel(newModel);
        LOGGER.debug("Took: {} ms", System.currentTimeMillis() - time);
    }

    public boolean isActive() {
        // Swing KeyboardTacletExtension.java:329-331
        return active.get();
    }

    public boolean isDirectMode() {
        // Swing KeyboardTacletExtension.java:333-335
        return directMode.get();
    }
}
