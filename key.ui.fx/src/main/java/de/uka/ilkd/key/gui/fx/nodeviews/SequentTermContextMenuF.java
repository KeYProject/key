/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeviews;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
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
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.join.ProspectivePartner;

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
 * Stage}. The milestone-deferred sections ({@code macro_menu}, {@code extension}, {@code smt}) are
 * rendered as disabled placeholders so the skeleton stays faithful; they are wired in later
 * milestones.
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
            // termmenu: TODO wire the focused-auto-mode activation (Swing
            // FocussedRuleApplicationAction) once the shift-click hit-test wiring lands (S3);
            // for now the item is a faithful disabled placeholder.
            case "focus_auto_mode" -> disabledItem(action.label());
            case "copy_clipboard" -> copyClipboardItem(ctx);
            case "name_creation_info" -> nameCreationInfoItem(action, ctx);
            case "no_rules" -> disabledItem(action.label());
            // termmenu: TODO these sections need the FX macro list (ProofMacroMenu), extension
            // registry (KeYGuiExtensionFacade) and SMT-launch plumbing — deferred milestones.
            // They are rendered as disabled placeholders so the menu structure stays faithful.
            case "macro_menu", "extension", "smt" -> disabledItem(action.label());
            default -> disabledItem(action.label());
        };
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
