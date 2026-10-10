/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeviews;

import java.io.File;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import javafx.geometry.Insets;
import javafx.scene.control.Button;
import javafx.scene.control.CustomMenuItem;
import javafx.scene.control.Label;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.TextArea;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.stage.Modality;
import javafx.stage.Stage;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.gui.fx.IssueDialogF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.ProofScriptWorkerF;
import de.uka.ilkd.key.gui.fx.keyshortcuts.KeyStrokeManagerF;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.FeatureSettings;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.reflection.ClassLoaderUtil;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * menu: MP8/B12 — shared construction of the proof-macro menu content (Swing {@code
 * ProofMacroMenu}, ProofMacroMenu.java). Three user-visible surfaces are backed by this factory
 * (so all three present the very same macros with the same look):
 * <ul>
 * <li>the sequent-view right-click macro popup (MP7, {@link SequentViewF#buildMacroPopup});</li>
 * <li>the term-menu "Strategy Macros" section (MP8b, {@link SequentTermContextMenuF}); and</li>
 * <li>the proof-tree context-menu "Strategy Macros" submenu (B12,
 * {@link de.uka.ilkd.key.gui.fx.prooftree.ProofTreeViewF}).</li>
 * </ul>
 * <p>
 * The content is the *superset* of the Swing menu: every registered macro
 * ({@link ProofMacroMenu#REGISTERED_MACROS}, the ServiceLoader list of
 * {@code META-INF/services/de.uka.ilkd.key.macros.ProofMacro}) whose {@link ProofMacro#canApplyTo}
 * accepts the clicked position, grouped by {@link ProofMacro#getCategory()} in first-appearance
 * order with separators between the groups (null category keys form their own group), followed by
 * the PROOF_SCRIPTS section ({@code "Run proof script from file..."} / {@code "Input proof
 * script..."}) when the feature is active (Swing ProofMacroMenu.java:81-134).
 * <p>
 * JavaFX {@link MenuItem} has no tooltip property (unlike Swing {@code JMenuItem.setToolTipText}),
 * so each macro item is a {@link CustomMenuItem} wrapping a tooltip-bearing {@link Label}
 * (Swing ProofMacroMenu.createMenuItem, ProofMacroMenu.java:143-144).
 */
public final class ProofMacroMenuF {

    private static final Logger LOGGER = LoggerFactory.getLogger(ProofMacroMenuF.class);

    private ProofMacroMenuF() {
    }

    /**
     * P3b/B12: all registered proof macros (Swing {@code ProofMacroMenu.REGISTERED_MACROS},
     * ProofMacroMenu.java:60-61: {@code ClassLoaderUtil.loadServices(ProofMacro.class)}) — the
     * superset that contains the four Automation-submenu macros of
     * {@link MainWindowF#AUTOMATION_MACROS}.
     */
    static final Iterable<ProofMacro> REGISTERED_MACROS =
        ClassLoaderUtil.loadServices(ProofMacro.class);

    /**
     * P3b/B12: the feature id gating the two proof-script entries (Swing
     * {@code ProofMacroMenu.FEATURE_PROOF_SCRIPTS}, ProofMacroMenu.java:63-64). Resolved from the
     * shared registry so the Swing and FX menus never register two features with the same id (the
     * FeatureSettingsPanel would then list twice, see the BULK_UI_TEST handling in MainWindowF).
     * Exposed for the persistent proof-tree macro submenu, which registers the live
     * {@code FeatureSettings.onAndActivate} listener ({@link ProofTreeViewF}).
     */
    public static final FeatureSettings.Feature PROOF_SCRIPTS_FEATURE =
        FeatureSettings.Feature.FEATURES.stream().filter(f -> "PROOF_SCRIPTS".equals(f.id()))
                .findFirst().orElseGet(() -> FeatureSettings.createFeature("PROOF_SCRIPTS"));

    /**
     * P3b/B12: the last directory of the script file chooser (Swing
     * {@code ProofScriptFromFileAction.lastDirectory}).
     */
    private static Path lastScriptDirectory;

    /**
     * menu: MP8 — a single macro item whose action runs the macro on the given node at the given
     * position (Swing {@code ProofMacroUserAction}, ProofMacroUserAction.java:57-59: {@code
     * mediator.getUI().getProofControl().runMacro(node, macro, pio)}; the core silently ignores
     * the run while auto mode is active, and {@code pio} may be {@code null} — a sequent position
     * may resolve to no occurrence and global macros accept that).
     *
     * @param macro the macro to run
     * @param node the node the macro is started at (the mediator's selection for the sequent
     *        menus; the invoked popup node for the proof-tree menu, see ProofTreeViewF)
     * @param proofControl the proof control to run the macro with
     * @param pio the clicked {@link PosInOccurrence}, possibly {@code null}
     * @return the wired macro menu item
     */
    public static MenuItem itemFor(ProofMacro macro, Node node, ProofControl proofControl,
            PosInOccurrence pio) {
        Label label = new Label(macro.getName());
        Tooltip.install(label, new Tooltip(macro.getDescription()));
        CustomMenuItem item = new CustomMenuItem(label);
        item.setOnAction(e -> proofControl.runMacro(node, macro, pio));
        // shortcuts (P1): macro accelerators on the menu items for global applications (Swing
        // ProofMacroMenu.createMenuItem, ProofMacroMenu.java:146-148: "currently only for global
        // macro applications")
        if (pio == null) {
            KeyStrokeManagerF.getInstance().binding(macro.getClass().getName())
                    .ifPresent(item::setAccelerator);
        }
        return item;
    }

    /**
     * P3b/B12: the flat, category-grouped menu content of the Swing {@code ProofMacroMenu}
     * (ProofMacroMenu.java:81-134): every registered macro whose {@code canApplyTo} accepts the
     * clicked position, grouped by category in first-appearance order with {@code
     * SeparatorMenuItem}s between the groups, plus the PROOF_SCRIPTS section when the feature is
     * active. The sequence of groups is therefore a superset of, and orders the four automation
     * macros exactly like, the FX Automation submenu's {@link MainWindowF#AUTOMATION_MACROS}.
     *
     * @param proof the proof of the clicked node
     * @param goals the enabled subtree goals of the node (Swing
     *        {@code node.proof().getSubtreeEnabledGoals(node)}, ProofMacroMenu.java:88-89)
     * @param node the node the macros run on
     * @param proofControl the proof control to run the macros with
     * @param pio the clicked {@link PosInOccurrence}, possibly {@code null}
     * @return the ordered menu items (macros + separators + optional script section)
     */
    public static List<MenuItem> items(Proof proof, ImmutableList<Goal> goals, Node node,
            ProofControl proofControl, @Nullable PosInOccurrence pio) {
        // Macros are grouped according to their category (Swing ProofMacroMenu.java:84-99).
        Map<String, List<MenuItem>> groups = new LinkedHashMap<>();
        for (ProofMacro macro : REGISTERED_MACROS) {
            if (macro.canApplyTo(proof, goals, pio)) {
                groups.computeIfAbsent(macro.getCategory(), x -> new ArrayList<>())
                        .add(itemFor(macro, node, proofControl, pio));
            }
        }
        List<MenuItem> result = new ArrayList<>();
        boolean first = true;
        for (List<MenuItem> group : groups.values()) {
            if (!first) {
                result.add(new SeparatorMenuItem());
            }
            first = false;
            result.addAll(group);
        }
        if (FeatureSettings.isFeatureActivated(PROOF_SCRIPTS_FEATURE)) {
            result.add(new SeparatorMenuItem());
            result.addAll(scriptSectionItems());
        }
        return result;
    }

    /**
     * P3b/B12: whether at least one registered macro {@code canApplyTo} the position (Swing
     * {@code ProofMacroMenu.isEmpty()}, ProofMacroMenu.java:160-162: the constructor counts the
     * applicable macros; an empty menu causes the callers to fall back to the term menu).
     */
    public static boolean anyApplicable(Proof proof, ImmutableList<Goal> goals,
            @Nullable PosInOccurrence pio) {
        for (ProofMacro macro : REGISTERED_MACROS) {
            if (macro.canApplyTo(proof, goals, pio)) {
                return true;
            }
        }
        return false;
    }

    /**
     * P3b/B12: the names of the {@code canApplyTo}-applicable macros at the given position, in
     * the same first-appearance category grouping the strategy-macro menus present (Swing
     * ProofMacroMenu.java:84-99 — exposed for the {@code key.fx.verify.prooftree} count seam:
     * the proof-tree macro submenu must present exactly these items, grouped like Swing).
     */
    public static List<String> applicableMacroNames(Proof proof, ImmutableList<Goal> goals,
            @Nullable PosInOccurrence pio) {
        Map<String, List<String>> groups = new LinkedHashMap<>();
        for (ProofMacro macro : REGISTERED_MACROS) {
            if (macro.canApplyTo(proof, goals, pio)) {
                groups.computeIfAbsent(macro.getCategory(), x -> new ArrayList<>())
                        .add(macro.getName());
            }
        }
        List<String> names = new ArrayList<>();
        for (List<String> group : groups.values()) {
            names.addAll(group);
        }
        return names;
    }

    /**
     * P3b/B12: the two PROOF_SCRIPTS entries (Swing {@code ProofScriptFromFileAction} / {@code
     * ProofScriptInputAction} created inline, ProofMacroMenu.java:115-117). The actions open the
     * script file chooser / input dialog, parse the script ({@link ParsingFacade}) and start the
     * {@link ProofScriptWorkerF} on the selected proof.
     */
    private static List<MenuItem> scriptSectionItems() {
        MenuItem fromFile = new MenuItem("Run proof script from file...");
        fromFile.setOnAction(e -> runScriptFromFileDialog());
        MenuItem input = new MenuItem("Input proof script...");
        input.setOnAction(e -> inputScriptDialog());
        return List.of(fromFile, input);
    }

    /**
     * P3b/B12: the script file chooser + worker start (Swing {@code
     * ProofScriptFromFileAction.actionPerformed}, ProofScriptFromFileAction.java:48-80).
     */
    private static void runScriptFromFileDialog() {
        MainWindowF window = MainWindowF.getInstance();
        if (window == null) {
            return;
        }
        Path dir = lastScriptDirectory;
        if (dir == null) {
            Proof currentProof = window.getMediator().getSelectedProof();
            Path currentFile = currentProof == null ? null : currentProof.getProofFile();
            dir = currentFile == null ? Paths.get(".") : currentFile.getParent();
        }
        FileChooser fc = new FileChooser();
        fc.setTitle("Select file to load");
        fc.setInitialDirectory(dir.toFile());
        File selectedFile = fc.showOpenDialog(window.getStage());
        if (selectedFile == null) {
            return;
        }
        lastScriptDirectory = selectedFile.getParentFile().toPath();
        try {
            KeyAst.ProofScript script = ParsingFacade.parseScript(selectedFile.toPath());
            new ProofScriptWorkerF(window.getMediator(), window.getUserInterfaceControl(), script,
                null, window.getStage()).start();
        } catch (Exception ex) {
            LOGGER.error("", ex);
            IssueDialogF.showExceptionDialog(window.getStage(), ex);
        }
    }

    /**
     * P3b/B12: the script input dialog (Swing {@code ProofScriptInputAction}, a JDialog with a
     * text area and an OK button, ProofScriptInputAction.java:52-79).
     */
    private static void inputScriptDialog() {
        MainWindowF window = MainWindowF.getInstance();
        if (window == null) {
            return;
        }
        Stage dialog = new Stage();
        dialog.initOwner(window.getStage());
        dialog.initModality(Modality.APPLICATION_MODAL);
        dialog.setTitle("Enter proof script");

        TextArea textArea = new TextArea();
        VBox.setVgrow(textArea, Priority.ALWAYS);
        Button okButton = new Button("OK");
        okButton.setOnAction(event -> {
            try {
                KeyAst.ProofScript script = ParsingFacade.parseScript(textArea.getText());
                dialog.close();
                Goal goal = window.getMediator().getSelectedGoal();
                new ProofScriptWorkerF(window.getMediator(), window.getUserInterfaceControl(),
                    script, goal, window.getStage()).start();
            } catch (Exception ex) {
                LOGGER.error("", ex);
                IssueDialogF.showExceptionDialog(window.getStage(), ex);
            }
        });
        VBox box = new VBox(8, textArea, okButton);
        box.setPadding(new Insets(8));
        dialog.setScene(new javafx.scene.Scene(box));
        dialog.setWidth(500);
        dialog.setHeight(400);
        dialog.showAndWait();
    }
}
