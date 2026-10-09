/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeviews;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import javafx.application.Platform;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ButtonType;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.TextInputDialog;
import javafx.scene.input.Clipboard;
import javafx.scene.input.ClipboardContent;
import javafx.stage.Window;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.KeYGuiExtensionFacadeF;
import de.uka.ilkd.key.gui.fx.join.JoinActionF;
import de.uka.ilkd.key.gui.fx.mergerule.MergeRuleMenuItemF;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF.AbbrevActionEntry;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF.BuiltInEntry;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF.Entry;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF.NamedAction;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF.SubMenuEntry;
import de.uka.ilkd.key.gui.fx.nodeviews.SequentMenuModelF.TacletEntry;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.NameCreationInfo;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.join.ProspectivePartner;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.smt.solvertypes.SolverType;

import org.key_project.prover.sequent.PosInOccurrence;

import org.jspecify.annotations.Nullable;

/**
 * The JavaFX {@link ContextMenu} shell for the sequent term context menu. It converts the tree of
 * pure model descriptors ({@link SequentMenuModelF.Entry}) produced by
 * {@link SequentMenuModelF#build} into a code-built JavaFX {@code ContextMenu} and wires each
 * item to the {@link ProofControl} application path (Swing {@code CurrentGoalViewMenu} /
 * {@code SequentViewMenu}).
 * <p>
 * The shell is pure JavaFX construction — no FXML — and keeps every side effect (rule application,
 * rule instantiation dialog, reprint of the sequent) behind the proof control or the supplied
 * {@link MenuContext} callbacks, so the item structure is unit-testable without a live {@code
 * Stage}. The milestone-wired sections ({@code macro_menu}, {@code extension}, {@code smt})
 * render their real content; the disabled placeholders remain only for fixed skeleton entries
 * without a handler ({@code no_rules}).
 */
public final class SequentTermContextMenuF {

    private SequentTermContextMenuF() {
    }

    /**
     * Everything the shell needs to build and dispatch a menu for the clicked position: the shared
     * mediator, the {@link ProofControl} to apply rules with, the goal, the clicked position, the
     * owner window for dialogs and a reprint callback invoked after a rule/abbreviation changed the
     * sequent.
     */
    public record MenuContext(@Nullable KeYMediatorF mediator, @Nullable ProofControl proofControl,
            @Nullable Goal goal, @Nullable PosInSequent pos, @Nullable Window owner,
            @Nullable Runnable afterApply) {
        public MenuContext {
            // normalize null callbacks to no-ops so builders never null-check
            afterApply = afterApply == null ? () -> {
            } : afterApply;
        }
    }

    /**
     * Builds the {@link ContextMenu} for the given model entries.
     *
     * @param entries the ordered model descriptors
     * @param ctx the application context (mediator, proof control, goal, position, owner, reprint)
     * @return the constructed and wired context menu
     */
    public static ContextMenu build(List<Entry> entries, MenuContext ctx) {
        ContextMenu menu = new ContextMenu();
        menu.getItems().addAll(buildItems(entries, ctx));
        return menu;
    }

    private static List<MenuItem> buildItems(List<Entry> entries, MenuContext ctx) {
        List<MenuItem> items = new ArrayList<>();
        for (Entry entry : entries) {
            switch (entry.kind()) {
                case TACLET -> items.add(tacletItem((TacletEntry) entry, ctx));
                case BUILT_IN -> items.add(builtInMenu((BuiltInEntry) entry, ctx));
                case SUB_MENU -> items.add(subMenu((SubMenuEntry) entry, ctx));
                case NAMED_ACTION -> items.add(namedActionItem((NamedAction) entry, ctx));
                case ABBREV_ACTION -> items.add(abbrevItem((AbbrevActionEntry) entry, ctx));
                case SEPARATOR -> items.add(new SeparatorMenuItem());
            }
        }
        return items;
    }

    private static MenuItem tacletItem(TacletEntry entry, MenuContext ctx) {
        MenuItem item = new MenuItem(entry.label());
        item.setOnAction(e -> {
            Goal goal = ctx.goal();
            PosInOccurrence pio = ctx.pos() == null ? null : ctx.pos().getPosInOccurrence();
            if (goal != null && ctx.proofControl() != null) {
                ctx.proofControl().selectedTaclet(entry.app().taclet(), goal, pio);
                ctx.afterApply().run();
            }
        });
        return item;
    }

    private static Menu builtInMenu(BuiltInEntry entry, MenuContext ctx) {
        // The model passes the sub-menu label only for the dual-contribution contract/loop rules;
        // the Swing original titles the menu with the rule's display name (Swing
        // CurrentGoalViewMenu.addBuiltInRuleItem: "new JMenu(builtInRule.displayName())").
        String name = entry.rule().displayName();
        Menu menu = new Menu(name);
        for (NamedAction action : entry.actions()) {
            boolean forced = "apply_builtin_forced".equals(action.id());
            MenuItem item = new MenuItem(action.label());
            item.setOnAction(e -> {
                Goal goal = ctx.goal();
                PosInOccurrence pio =
                    ctx.pos() == null ? null : ctx.pos().getPosInOccurrence();
                if (goal != null && ctx.proofControl() != null) {
                    ctx.proofControl().selectedBuiltInRule(goal, entry.rule(), pio, forced, true);
                    ctx.afterApply().run();
                }
            });
            menu.getItems().add(item);
        }
        return menu;
    }

    private static Menu subMenu(SubMenuEntry entry, MenuContext ctx) {
        Menu menu = new Menu(entry.label());
        menu.getItems().addAll(buildItems(entry.children(), ctx));
        return menu;
    }

    private static MenuItem namedActionItem(NamedAction action, MenuContext ctx) {
        return switch (action.id()) {
            case "join" -> joinItem(action, ctx);
            case "merge_rule" -> mergeItem(action, ctx);
            // menu: MP8 — the focused-auto-mode activation is wired (Swing
            // FocussedRuleApplicationAction, FocussedAutoModeUserAction.java:43: {@code
            // mediator.getUI().getProofControl().startFocussedAutoMode(pio, goal)}); unlike the
            // Swing entry there is no separate caret to remember — the clicked position is the
            // focus, mirroring the shift+left-click fast path (CurrentGoalViewListener.java:57).
            case "focus_auto_mode" -> focusAutoModeItem(action, ctx);
            case "copy_clipboard" -> copyClipboardItem(ctx);
            case "name_creation_info" -> nameCreationInfoItem(action, ctx);
            case "no_rules" -> disabledItem(action.label());
            // menu: MP8 — the Strategy Macros section is wired (Swing ProofMacroMenu,
            // ProofMacroMenu.java:81: JMenu("Strategy Macros") with one item per applicable
            // macro); the extension and smt notes follow below.
            case "macro_menu" -> macroMenu(action, ctx);
            // extension: MP9.0 — the extension section is wired through the FX extension
            // facade (Swing KeYGuiExtension.ContextMenu for ContextMenuKind.SEQUENT_VIEW,
            // KeYGuiExtensionFacade.createTermMenu, KeYGuiExtensionFacade.java:271-277: the
            // extension actions of every provider are grouped into the "Extensions" sub-menu);
            // the disabled placeholder stays only when there are no contributions or no
            // position.
            case "extension" -> extensionSection(action, ctx);
            // menu: MP8 — SMT section item, wired in MP8c (Swing CurrentGoalViewMenu.
            // createSMTMenu, CurrentGoalViewMenu.java:219-231, SMTAction :765-790).
            case "smt" -> smtItem(action, ctx);
            default -> disabledItem(action.label());
        };
    }

    /**
     * The focused-auto-mode entry: starts an automatic proof search restricted to the clicked
     * position (Swing FocussedRuleApplicationAction, FocussedAutoModeUserAction.java:43: {@code
     * mediator.getUI().getProofControl().startFocussedAutoMode(pio, goal)}). The FX sequent view
     * is single-caret, so the clicked position <em>is</em> the focus — no separate caret state to
     * read (the Swing action takes it from {@code SequentView.getCaretPosition()},
     * FocussedAutoModeUserAction.java:39-40).
     */
    private static MenuItem focusAutoModeItem(NamedAction action, MenuContext ctx) {
        MenuItem item = new MenuItem(action.label());
        item.setOnAction(e -> {
            Goal goal = ctx.goal();
            PosInOccurrence pio = ctx.pos() == null ? null : ctx.pos().getPosInOccurrence();
            if (goal != null && ctx.proofControl() != null) {
                ctx.proofControl().startFocussedAutoMode(pio, goal);
                ctx.afterApply().run();
            }
        });
        return item;
    }

    /**
     * menu: MP8 — the "Strategy Macros" section (Swing {@code ProofMacroMenu}, a {@code
     * JMenu("Strategy Macros")}, ProofMacroMenu.java:81, with one item per applicable macro;
     * CurrentGoalViewMenu.addMacroMenu adds it to the term menu, CurrentGoalViewMenu.java:
     * 212-217). The FX model emits the section unconditionally (SequentMenuModelF.compute), so
     * all four macros of the Automation submenu / right-click popup ({@code
     * MainWindowF.AUTOMATION_MACROS}, same order as Swing MainWindow.createAutomationActions,
     * MainWindow.java:814-827) are shown — Swing instead filters by {@code canApplyTo} and
     * omits the whole menu when it is empty; with the model's fixed skeleton the section keeps
     * its label either way. Each item is built by the shared {@link ProofMacroMenuF} helper.
     */
    private static MenuItem macroMenu(NamedAction action, MenuContext ctx) {
        Node node = ctx.mediator() == null ? null : ctx.mediator().getSelectedNode();
        if (node == null || ctx.proofControl() == null) {
            // no proof context: keep the faithful disabled placeholder
            return disabledItem(action.label());
        }
        Menu menu = new Menu(action.label());
        PosInOccurrence pio = ctx.pos() == null ? null : ctx.pos().getPosInOccurrence();
        for (ProofMacro macro : MainWindowF.AUTOMATION_MACROS) {
            menu.getItems().add(ProofMacroMenuF.itemFor(macro, node, ctx.proofControl(), pio));
        }
        return menu;
    }

    /**
     * extension: MP9.0 — the "Extensions" section of the term menu (Swing
     * KeYGuiExtensionFacade.createTermMenu, KeYGuiExtensionFacade.java:271-277: the
     * SEQUENT_VIEW context actions of every provider are grouped into an "Extensions"
     * sub-menu of the term menu). When the clicked position is available and the providers
     * contribute items, the section renders them ENABLED inside the sub-menu; the disabled
     * placeholder stays only when there are no contributions — or no position, the fallback
     * exercised by the {@code key.fx.verify.extensions} self test.
     */
    private static MenuItem extensionSection(NamedAction action, MenuContext ctx) {
        if (ctx.pos() == null || ctx.mediator() == null || ctx.goal() == null) {
            return disabledItem(action.label());
        }
        List<MenuItem> items =
            KeYGuiExtensionFacadeF.getSequentContextItems(ctx.mediator(), ctx.goal(), ctx.pos());
        if (items.isEmpty()) {
            return disabledItem(action.label());
        }
        Menu menu = new Menu(action.label());
        menu.getItems().addAll(items);
        return menu;
    }

    /** Delayed-cut join (Swing JoinMenuItem / CurrentGoalViewMenu.createDelayedCutJoinMenu). */
    private static MenuItem joinItem(NamedAction action, MenuContext ctx) {
        MenuItem item = new MenuItem(action.label());
        item.setOnAction(e -> {
            Proof proof = ctx.goal() == null ? null : ctx.goal().proof();
            Object payload = action.payload();
            if (payload instanceof Collection<?> coll && proof != null
                    && ctx.proofControl() != null) {
                try {
                    @SuppressWarnings("unchecked")
                    List<ProspectivePartner> partners =
                        new ArrayList<>((Collection<ProspectivePartner>) coll);
                    JoinActionF.run(partners, proof, ctx.proofControl(), ctx.owner());
                } catch (RuntimeException ex) {
                    // The join dialog may fail to open (e.g. a missing stage owner in tests);
                    // never let a broken dialog take the context menu down with it.
                    System.err.println("Delayed-cut join could not be started: " + ex);
                    ex.printStackTrace();
                }
            }
        });
        return item;
    }

    /** State-merging rule (Swing MergeRuleMenuItem / CurrentGoalViewMenu.createMergeRuleMenu). */
    private static MenuItem mergeItem(NamedAction action, MenuContext ctx) {
        Goal goal = ctx.goal();
        PosInOccurrence pio = action.payload() instanceof PosInOccurrence p ? p : null;
        if (goal == null || pio == null || ctx.proofControl() == null) {
            return disabledItem(action.label());
        }
        return new MergeRuleMenuItemF(goal, pio, ctx.proofControl());
    }

    /** Copy the clicked term to the system clipboard (Swing SequentView.addClipboardItem). */
    private static MenuItem copyClipboardItem(MenuContext ctx) {
        MenuItem item = new MenuItem("Copy to clipboard");
        item.setOnAction(e -> {
            PosInSequent pos = ctx.pos();
            PosInOccurrence occ = pos == null ? null : pos.getPosInOccurrence();
            if (occ != null && occ.subTerm() != null) {
                String s = occ.subTerm().toString().replace('\u00A0', ' ');
                ClipboardContent content = new ClipboardContent();
                content.putString(s);
                Clipboard.getSystemClipboard().setContent(content);
            }
        });
        return item;
    }

    /**
     * View the {@link NameCreationInfo} of the clicked program variable (Swing
     * NameCreationInfoAction).
     */
    private static MenuItem nameCreationInfoItem(NamedAction action, MenuContext ctx) {
        MenuItem item = new MenuItem(action.label());
        item.setOnAction(e -> {
            Object payload = action.payload();
            String message;
            if (payload instanceof ProgramVariable var) {
                ProgramElementName name = var.getProgramElementName();
                NameCreationInfo info = name.getCreationInfo();
                message = info != null ? info.infoAsString() : "No information available.";
            } else {
                message = "No information available.";
            }
            Alert alert = new Alert(AlertType.INFORMATION, message, ButtonType.OK);
            alert.setTitle("Name creation info");
            alert.setHeaderText(null);
            if (ctx.owner() != null) {
                alert.initOwner(ctx.owner());
            }
            alert.showAndWait();
        });
        return item;
    }

    /**
     * Create / change / enable / disable an abbreviation for the clicked term via the shared
     * {@code NotationInfo.getAbbrevMap()} (Swing CurrentGoalViewMenu.createAbbrevSection and the
     * four AbbreviationActions).
     */
    private static MenuItem abbrevItem(AbbrevActionEntry entry, MenuContext ctx) {
        MenuItem item = new MenuItem(entry.label());
        item.setOnAction(e -> {
            PosInOccurrence occ = ctx.pos() == null ? null : ctx.pos().getPosInOccurrence();
            if (occ == null || occ.posInTerm() == null || ctx.mediator() == null) {
                return;
            }
            JTerm term = (JTerm) occ.subTerm();
            AbbrevMap map = ctx.mediator().getNotationInfo().getAbbrevMap();
            switch (entry.action()) {
                case CREATE -> createAbbreviation(map, term, ctx);
                case CHANGE -> changeAbbreviation(map, term, ctx);
                case ENABLE -> {
                    map.setEnabled(term, true);
                    ctx.afterApply().run();
                }
                case DISABLE -> {
                    map.setEnabled(term, false);
                    ctx.afterApply().run();
                }
            }
        });
        return item;
    }

    private static void createAbbreviation(AbbrevMap map, JTerm term, MenuContext ctx) {
        String old = term.toString();
        String trimmed = old.length() > 200 ? old.substring(0, 200) : old;
        TextInputDialog dialog = new TextInputDialog("");
        dialog.setTitle("New Abbreviation");
        dialog.setHeaderText(null);
        dialog.setContentText("Enter abbreviation for term: \n" + trimmed);
        dialog.setGraphic(null);
        if (ctx.owner() != null) {
            dialog.initOwner(ctx.owner());
        }
        dialog.showAndWait().ifPresent(abbreviation -> {
            if (invalidAbbreviation(abbreviation)) {
                showError("Only letters, numbers and '_' are allowed for Abbreviations", "Sorry",
                    ctx.owner());
                return;
            }
            try {
                if (map.containsAbbreviation(abbreviation)) {
                    String newAbbreviation = "old_" + abbreviation;
                    ButtonType choice = showConfirm(
                        String.format(
                            "Abbreviation %s already bound. Do want to rename the previous "
                                + "binding to %s and proceed?",
                            abbreviation, newAbbreviation),
                        "Name collision resolution", ctx.owner());
                    if (choice != ButtonType.OK) {
                        return;
                    }
                    var prevTerm = map.getTerm(abbreviation);
                    var enabled = prevTerm != null && map.isEnabled(prevTerm);
                    if (prevTerm != null) {
                        map.remove(prevTerm);
                    }
                    if (prevTerm != null) {
                        map.put(prevTerm, newAbbreviation, enabled);
                    }
                }
                map.put(term, abbreviation, true);
                ctx.afterApply().run();
            } catch (AbbrevException sce) {
                showError(sce.getMessage(), "Sorry", ctx.owner());
            }
        });
    }

    private static void changeAbbreviation(AbbrevMap map, JTerm term, MenuContext ctx) {
        String current = map.getAbbrev(term);
        String initial = current != null && current.length() > 1 ? current.substring(1) : "";
        TextInputDialog dialog = new TextInputDialog(initial);
        dialog.setTitle("Change Abbreviation");
        dialog.setHeaderText(null);
        dialog.setContentText("Enter abbreviation for term: \n" + term);
        dialog.setGraphic(null);
        if (ctx.owner() != null) {
            dialog.initOwner(ctx.owner());
        }
        dialog.showAndWait().ifPresent(abbreviation -> {
            if (abbreviation == null) {
                return;
            }
            if (invalidAbbreviation(abbreviation)) {
                showError("Only letters, numbers and '_' are allowed for Abbreviations", "Sorry",
                    ctx.owner());
                return;
            }
            try {
                map.changeAbbrev(term, abbreviation);
                ctx.afterApply().run();
            } catch (AbbrevException sce) {
                showError(sce.getMessage(), "Sorry", ctx.owner());
            }
        });
    }

    private static boolean invalidAbbreviation(String s) {
        if (s == null || s.isBlank()) {
            return true;
        }
        return !s.chars()
                .allMatch(it -> Character.isAlphabetic(it) || Character.isDigit(it) || it == '_');
    }

    private static MenuItem disabledItem(String label) {
        MenuItem item = new MenuItem(label);
        item.setDisable(true);
        return item;
    }

    /**
     * menu: MP8 — the SMT section item: runs the given solver union on the clicked goal's
     * sequent (Swing {@code CurrentGoalViewMenu.SMTAction}, CurrentGoalViewMenu.java:765-790: a
     * background thread builds a {@code DefaultSMTSettings}, a {@code SolverLauncher} with a
     * listener, an {@code SMTProblem} for the goal and launches the union's solver types on the
     * goal's services, then shows the outcome). Swing presents the outcome in the heavy
     * {@code FullSmtSolverDialog} (progress dialog + countermodel application); the FX minimum
     * shows a read-only result dialog with each solver's outcome and the combined final result —
     * the counterexample-application UI of the Swing dialog is not ported.
     */
    private static MenuItem smtItem(NamedAction action, MenuContext ctx) {
        MenuItem item = new MenuItem(action.label());
        item.setOnAction(e -> runSmt(action, ctx));
        return item;
    }

    /**
     * menu: MP8 — launches the solver union of the SMT item on the clicked goal (Swing
     * CurrentGoalViewMenu.SMTAction.actionPerformed, CurrentGoalViewMenu.java:773-789). The
     * launch is synchronous and blocking (SolverLauncher.launch waits for every solver), so it
     * runs in a daemon thread; the read-only result dialog is presented back on the FX thread.
     */
    private static void runSmt(NamedAction action, MenuContext ctx) {
        Goal goal = ctx.goal();
        if (goal == null || !(action.payload() instanceof SolverTypeCollection union)) {
            return;
        }
        Window owner = ctx.owner();
        Thread thread = new Thread(() -> {
            DefaultSMTSettings settings =
                new DefaultSMTSettings(goal.proof().getSettings().getSMTSettings(),
                    ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings(),
                    goal.proof().getSettings().getNewSMTSettings(), goal.proof());
            SolverLauncher launcher = new SolverLauncher(settings);
            // a listener suppresses the launcher's SolverException for failing solvers
            // (SolverLauncher.notifyListenersOfStop, SolverLauncher.java:370-376); Swing's
            // SolverListener plays the same role (CurrentGoalViewMenu.java:783)
            launcher.addListener(new SolverLauncherListener() {
                @Override
                public void launcherStopped(SolverLauncher launcher,
                        Collection<SMTSolver> finishedSolvers) {
                }

                @Override
                public void launcherStarted(Collection<SMTProblem> problems,
                        Collection<SolverType> solverTypes, SolverLauncher launcher) {
                }
            });
            SMTProblem problem = new SMTProblem(goal);
            String report;
            try {
                launcher.launch(union.getTypes(), List.of(problem),
                    goal.proof().getServices());
                StringBuilder sb = new StringBuilder();
                for (SMTSolver solver : problem.getSolvers()) {
                    SMTSolverResult result = solver.getFinalResult();
                    sb.append(solver.name()).append(": ")
                            .append(result == null ? "no result" : result.isValid()).append("\n");
                }
                sb.append("\n").append(problem.getFinalResult().isValid());
                report = sb.toString();
            } catch (RuntimeException ex) {
                report = "SMT run failed: " + ex;
            }
            String finalReport = report;
            Platform.runLater(() -> showSmtResult(union.toString(), finalReport, owner));
        }, "SMTRunner");
        thread.setDaemon(true);
        thread.start();
    }

    /**
     * menu: MP8 — read-only SMT result dialog (the FX minimum replacing the heavy Swing
     * FullSmtSolverDialog progress/countermodel UI).
     */
    private static void showSmtResult(String unionName, String report, Window owner) {
        Alert alert = new Alert(AlertType.INFORMATION, report, ButtonType.OK);
        alert.setTitle("SMT: " + unionName);
        alert.setHeaderText(null);
        if (owner != null) {
            alert.initOwner(owner);
        }
        alert.showAndWait();
    }

    private static void showError(String message, String title, Window owner) {
        Alert alert = new Alert(AlertType.ERROR, message, ButtonType.OK);
        alert.setTitle(title);
        alert.setHeaderText(null);
        if (owner != null) {
            alert.initOwner(owner);
        }
        alert.showAndWait();
    }

    private static ButtonType showConfirm(String message, String title, Window owner) {
        Alert alert = new Alert(AlertType.CONFIRMATION, message, ButtonType.OK,
            ButtonType.CANCEL);
        alert.setTitle(title);
        alert.setHeaderText(null);
        if (owner != null) {
            alert.initOwner(owner);
        }
        alert.showAndWait();
        return alert.getResult();
    }
}
