/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.contractcompletions;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.SplitPane;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TextArea;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Stage;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.statement.LoopStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.PrettyPrinter;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.javafx.FxUtil;

/**
 * contractcompletions (P2b): JavaFX port of the Swing {@code InvariantConfigurator}
 * (InvariantConfigurator.java, 1043 lines) — the interactive loop-invariant editor of the loop
 * invariant rule ({@code LoopInvariantRuleCompletion}). The singleton keeps the per-loop
 * candidate invariants ({@code mapLoopsToInvariants}), the dialog shows one tab per candidate
 * invariant with per-heap sub-tabs for the invariant and modifiable clauses, the variant field
 * and the information-flow fields, live-parses every edit (status panel, Apply/Store disabled
 * on error) and builds the new specification via
 * {@link LoopSpecification#configurate}. Cancel throws {@link RuleAbortException} like in
 * Swing.
 * <p>
 * Deviations: the error/status panel is updated in place (the Swing dialog rebuilds it on every
 * parse); the FX dialog uses application modality without owner
 * ({@link ContractConfiguratorF}); the abbreviations of the editor notation info are wired via
 * {@link #setAbbrevMap} (Swing reads them from the mediator at dialog construction).
 */
public class InvariantConfiguratorF {

    private static final int INV_IDX = 0;
    private static final int MOD_IDX = 1;
    private static final int VAR_IDX = 2;
    private static final int IF_PRE_IDX = 3;
    private static final int IF_POST_IDX = 4;
    private static final int IF_OO_IDX = 5;
    private static final String DEFAULT = "Default";

    private static InvariantConfiguratorF configurator = null;

    /** the abbreviation map used by the parser (Swing: mediator notation info). */
    private static AbbrevMap abbrevMap = new AbbrevMap();

    private List<Map<String, String>[]> invariants;
    private final Map<LoopStatement, List<Map<String, String>[]>> mapLoopsToInvariants =
        new LinkedHashMap<>();
    private int index = 0;
    private LoopSpecification newInvariant = null;
    private boolean userPressedCancel = false;

    /** Swing singleton. */
    public static InvariantConfiguratorF getInstance() {
        if (configurator == null) {
            configurator = new InvariantConfiguratorF();
        }
        return configurator;
    }

    /**
     * Wires the abbreviation map (the Swing dialog reads the mediator's notation info at
     * construction; the FX port takes it once at startup from MainWindowF).
     *
     * @param map the abbreviation map, may be {@code null} for an empty map
     */
    public static void setAbbrevMap(AbbrevMap map) {
        abbrevMap = map == null ? new AbbrevMap() : map;
    }

    /** The current abbreviation map (verification harness, Swing {@code getAbbrevMap}). */
    public static AbbrevMap getAbbrevMap() {
        return abbrevMap;
    }

    /**
     * Opens the dialog and returns the user-edited loop invariant (Swing
     * {@code getLoopInvariant}, InvariantConfigurator.java:93-1037).
     *
     * @param loopInv the {@link LoopSpecification} (complete or partial) to be displayed and
     *        edited
     * @param services the services
     * @param requiresVariant whether termination shall be proven (variant required)
     * @param heapContext the relevant heaps (the enabled sub-tabs)
     * @return the user-edited loop invariant
     * @throws RuleAbortException if the user cancelled the dialog
     */
    public LoopSpecification getLoopInvariant(final LoopSpecification loopInv,
            final Services services, final boolean requiresVariant,
            final List<LocationVariable> heapContext) throws RuleAbortException {
        if (loopInv == null) {
            return null;
        }
        index = 0;
        InvariantDialogF dialog =
            new InvariantDialogF(loopInv, services, requiresVariant, heapContext);
        dialog.show();
        if (userPressedCancel) {
            throw new RuleAbortException(
                "Interactive invariant configuration canceled by user.");
        }
        return newInvariant;
    }

    /**
     * The FX dialog (Swing inner class {@code InvariantDialog}). One top tab per candidate
     * invariant, each with the per-heap invariant/modifiable sub-tabs, the variant field and
     * the information-flow fields; the left side shows the loop source and the status panel.
     */
    private final class InvariantDialogF {

        private final LoopSpecification loopInv;
        private final Services services;
        private final boolean requiresVariant;
        private final List<LocationVariable> heapContext;
        private final KeyIO parser;

        private final Stage stage = new Stage();
        private final TabPane inputPane = new TabPane();
        private final Map<String, TextArea> invariantStatus = new LinkedHashMap<>();
        private final Map<String, TextArea> modifiableStatus = new LinkedHashMap<>();
        private final TextArea variantStatus = new TextArea();

        private final Button applyButton = new Button("Apply");
        private final Button storeButton = new Button("Store");

        private JTerm variantTerm = null;
        private final Map<LocationVariable, JTerm> modifiableTerm = new LinkedHashMap<>();
        private final Map<LocationVariable, JTerm> freeModifiableTerm = new LinkedHashMap<>();
        private final Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs =
            new LinkedHashMap<>();
        private final Map<LocationVariable, JTerm> invariantTerm = new LinkedHashMap<>();
        private final Map<LocationVariable, JTerm> freeInvariantTerm = new LinkedHashMap<>();

        InvariantDialogF(LoopSpecification loopInv, Services services, boolean requiresVariant,
                List<LocationVariable> heapContext) {
            this.loopInv = loopInv;
            this.services = services;
            this.requiresVariant = requiresVariant;
            this.heapContext = heapContext;

            initInvariants();

            // left side: loop source (Swing initLoopPresentation, InvariantConfigurator:555-571)
            TextArea loopRep = new TextArea();
            PrettyPrinter printer = PrettyPrinter.purePrinter();
            printer.print(loopInv.getLoop());
            loopRep.setText(printer.result());
            loopRep.setEditable(false);
            loopRep.getStyleClass().add("invariant-loop-representation");
            VBox loopBox = new VBox(titled("Loop", loopRep));
            VBox.setVgrow(loopRep, Priority.ALWAYS);
            VBox statusBox = new VBox(4);
            statusBox.setPadding(new Insets(4));
            for (LocationVariable heap : allHeaps()) {
                String k = heap.toString();
                boolean base = heap == baseHeap();
                TextArea invStatus = createStatusArea(
                    "Invariant" + (base ? "" : "[" + k + "]") + " - Status:");
                TextArea modStatus = createStatusArea(
                    "Modifiable" + (base ? "" : "[" + k + "]") + " - Status:");
                invariantStatus.put(k, invStatus);
                modifiableStatus.put(k, modStatus);
                statusBox.getChildren().addAll(invStatus, modStatus);
            }
            variantStatus.setPrefRowCount(2);
            variantStatus.setEditable(false);
            variantStatus.getStyleClass().add("invariant-status-ok");
            statusBox.getChildren().add(titled("Variant - Status", variantStatus));

            // right side: one tab per candidate invariant (Swing initInputPane, :188-198)
            for (int i = 0; i < invariants.size(); i++) {
                inputPane.getTabs().add(new Tab("Inv " + i, createInvariantTab(i)));
            }
            inputPane.getSelectionModel().selectedIndexProperty()
                    .addListener((obs, oldIndex, newIndex) -> {
                        index = newIndex.intValue();
                        parse();
                    });

            BorderPane root = new BorderPane();
            SplitPane split = new SplitPane(loopBox, inputPane);
            split.setDividerPositions(0.35);
            root.setCenter(split);
            root.setBottom(statusBox);

            HBox buttonPanel = new HBox(5, applyButton, storeButton,
                cancelButton());
            buttonPanel.setAlignment(Pos.CENTER_RIGHT);
            buttonPanel.setPadding(new Insets(5));
            root.setTop(buttonPanel);

            applyButton.setOnAction(e -> applyActionPerformed());
            storeButton.setOnAction(e -> storeActionPerformed());

            NamespaceSet nss = services.getNamespaces().copyWithParent();
            parser = new KeyIO(services, nss);
            parser.setAbbrevMap(abbrevMap);

            stage.setTitle("Invariant Configurator");
            Scene scene = new Scene(root, 1100, 750);
            ThemeManager.getInstance().style(scene);
            stage.setScene(scene);
            parse();
        }

        private Button cancelButton() {
            Button cancelButton = new Button("Cancel");
            cancelButton.setOnAction(e -> cancelActionPerformed());
            return cancelButton;
        }

        private <T extends javafx.scene.Node> javafx.scene.control.TitledPane titled(String text,
                T content) {
            javafx.scene.control.TitledPane pane =
                new javafx.scene.control.TitledPane(text, content);
            pane.setCollapsible(false);
            return pane;
        }

        private TextArea createStatusArea(String title) {
            TextArea area = new TextArea();
            area.setEditable(false);
            area.setPrefRowCount(2);
            area.setText("OK");
            area.getStyleClass().add("invariant-status-ok");
            return area;
        }

        // ------------------------------------------------------------------
        // data setup (Swing initInvariants, InvariantConfigurator.java:200-326)
        // ------------------------------------------------------------------

        private ImmutableList<LocationVariable> allHeaps() {
            return services.getTypeConverter().getHeapLDT().getAllHeaps();
        }

        private LocationVariable baseHeap() {
            return services.getTypeConverter().getHeapLDT().getHeap();
        }

        private String printTerm(JTerm t, boolean pretty) {
            // Swing wrapper for the pretty printer (InvariantConfigurator.java:332-337);
            // the boolean is the "short attr notation" flag of OutputStreamProofSaver
            return OutputStreamProofSaver.printTerm(t, services, !pretty);
        }

        @SuppressWarnings("unchecked")
        private void initInvariants() {
            Map<String, String>[] loopInvTexts = new Map[IF_OO_IDX + 1];

            loopInvTexts[INV_IDX] = new LinkedHashMap<>();
            Map<LocationVariable, JTerm> atPres = loopInv.getInternalAtPres();
            for (LocationVariable heap : allHeaps()) {
                JTerm invariant =
                    loopInv.getInvariant(heap, loopInv.getInternalSelfTerm(), atPres, services);
                if (invariant == null) {
                    loopInvTexts[INV_IDX].put(heap.toString(), "true");
                } else {
                    loopInvTexts[INV_IDX].put(heap.toString(), printTerm(invariant, true));
                }
            }

            loopInvTexts[MOD_IDX] = new LinkedHashMap<>();
            for (LocationVariable heap : allHeaps()) {
                JTerm modifiable =
                    loopInv.getModifiable(heap, loopInv.getInternalSelfTerm(), atPres, services);
                if (modifiable == null) {
                    loopInvTexts[MOD_IDX].put(heap.toString(), "allLocs");
                } else {
                    // pretty syntax cannot be parsed yet for modifiable
                    loopInvTexts[MOD_IDX].put(heap.toString(), printTerm(modifiable, false));
                }
            }

            loopInvTexts[VAR_IDX] = new LinkedHashMap<>();
            JTerm variant = loopInv.getVariant(loopInv.getInternalSelfTerm(), atPres, services);
            if (variant == null) {
                loopInvTexts[VAR_IDX].put(DEFAULT, "");
            } else {
                loopInvTexts[VAR_IDX].put(DEFAULT, printTerm(variant, true));
            }

            loopInvTexts[IF_PRE_IDX] = new LinkedHashMap<>();
            loopInvTexts[IF_POST_IDX] = new LinkedHashMap<>();
            loopInvTexts[IF_OO_IDX] = new LinkedHashMap<>();
            for (LocationVariable heap : allHeaps()) {
                ImmutableList<InfFlowSpec> specs =
                    loopInv.getInfFlowSpecs(heap, loopInv.getInternalSelfTerm(), atPres, services);
                if (specs == null) {
                    loopInvTexts[IF_PRE_IDX].put(heap.toString(), "true");
                    loopInvTexts[IF_POST_IDX].put(heap.toString(), "true");
                    loopInvTexts[IF_OO_IDX].put(heap.toString(), "true");
                } else {
                    for (InfFlowSpec spec : specs) {
                        for (JTerm t : spec.preExpressions) {
                            loopInvTexts[IF_PRE_IDX].put(heap.toString(), printTerm(t, false));
                        }
                        for (JTerm t : spec.postExpressions) {
                            loopInvTexts[IF_POST_IDX].put(heap.toString(), printTerm(t, false));
                        }
                        for (JTerm t : spec.newObjects) {
                            loopInvTexts[IF_OO_IDX].put(heap.toString(), printTerm(t, false));
                        }
                    }
                }
            }

            // Swing: the candidate invariants are kept per loop across invocations (:328-349)
            if (!mapLoopsToInvariants.containsKey(loopInv.getLoop())) {
                invariants = new ArrayList<>();
                invariants.add(loopInvTexts);
                mapLoopsToInvariants.put(loopInv.getLoop(), invariants);
                index = invariants.size() - 1;
            } else {
                invariants = mapLoopsToInvariants.get(loopInv.getLoop());
                if (!invariants.contains(loopInvTexts)) {
                    invariants.add(loopInvTexts);
                    index = invariants.size() - 1;
                } else {
                    index = invariants.indexOf(loopInvTexts);
                }
            }
        }

        // ------------------------------------------------------------------
        // UI construction (Swing createInvariantTab, InvariantConfigurator.java:340-446)
        // ------------------------------------------------------------------

        private String heapTitle(String template, String key) {
            return String.format(template,
                key.equals(HeapLDT.BASE_HEAP_NAME.toString()) ? "" : "[" + key + "]");
        }

        private VBox createInvariantTab(int i) {
            VBox panel = new VBox(4);
            panel.setPadding(new Insets(4));

            Map<String, String> invs = invariants.get(i)[INV_IDX];
            TabPane invPane = heapPane(invs, "Invariant%s: ", (area, k) -> {
                area.textProperty().addListener((obs, o, n) -> textUpdate(INV_IDX, k, n));
            }, i);

            Map<String, String> mods = invariants.get(i)[MOD_IDX];
            TabPane modPane = heapPane(mods, "Modifiable%s: ", (area, k) -> {
                area.textProperty().addListener((obs, o, n) -> textUpdate(MOD_IDX, k, n));
            }, i);

            TextArea varArea = inputArea("Variant" + ": ",
                invariants.get(i)[VAR_IDX].get(DEFAULT));
            varArea.textProperty()
                    .addListener((obs, o, n) -> textUpdate(VAR_IDX, DEFAULT, n));

            Map<String, String> pres = invariants.get(i)[IF_PRE_IDX];
            TabPane prePane = heapPane(pres, "InfFlowPreExpressions%s: ", (area, k) -> {
                area.textProperty().addListener((obs, o, n) -> textUpdate(IF_PRE_IDX, k, n));
            }, i);

            Map<String, String> posts = invariants.get(i)[IF_POST_IDX];
            TabPane postPane = heapPane(posts, "InfFlowPostExpressions%s: ", (area, k) -> {
                area.textProperty().addListener((obs, o, n) -> textUpdate(IF_POST_IDX, k, n));
            }, i);

            Map<String, String> newObs = invariants.get(i)[IF_OO_IDX];
            TabPane newObsPane = heapPane(newObs, "InfFlowNewObjects%s: ", (area, k) -> {
                area.textProperty().addListener((obs, o, n) -> textUpdate(IF_OO_IDX, k, n));
            }, i);

            panel.getChildren().addAll(invPane, modPane, varArea, prePane, postPane, newObsPane);
            return panel;
        }

        private interface TextAreaConfigurator {
            void configure(TextArea area, String key);
        }

        /**
         * One bottom tab pane per heap with a titled input area (Swing creates the same
         * per-heap panes for invariant/modifiable/inf-flow fields).
         */
        private TabPane heapPane(Map<String, String> values, String titleTemplate,
                TextAreaConfigurator configurator, int tabIndex) {
            TabPane pane = new TabPane();
            pane.setTabClosingPolicy(TabPane.TabClosingPolicy.UNAVAILABLE);
            for (String k : values.keySet()) {
                TextArea area = inputArea(heapTitle(titleTemplate, k), values.get(k));
                configurator.configure(area, k);
                Tab tab = new Tab(k, area);
                // Swing updateActiveTabs: only the heaps of the context are enabled (:959-967)
                tab.setDisable(heapContext.stream()
                        .noneMatch(lv -> lv.name().toString().equals(k)));
                pane.getTabs().add(tab);
            }
            pane.getStyleClass().add("invariant-heap-pane");
            return pane;
        }

        /** Swing {@code createInputTextArea}: a titled editable area. */
        private TextArea inputArea(String title, String text) {
            TextArea area = new TextArea(text);
            area.setPrefRowCount(3);
            area.getStyleClass().add("invariant-input");
            return area;
        }

        // ------------------------------------------------------------------
        // update actions (Swing invUpdatePerformed & friends, :706-789)
        // ------------------------------------------------------------------

        private void textUpdate(int kindIdx, String key, String text) {
            index = inputPane.getSelectionModel().getSelectedIndex();
            Map<String, String>[] inv = invariants.get(index);
            inv[kindIdx].put(key, text);
            parse();
        }

        // ------------------------------------------------------------------
        // parse + build (Swing parse/buildInvariant, :815-957)
        // ------------------------------------------------------------------

        private static RuntimeException newUnexpectedTypeException(Sort expected, Sort actual) {
            return new IllegalStateException(
                String.format("Entered formula is expected of type %s but got %s.", expected,
                    actual));
        }

        /** Swing {@code parseInvariant}: the invariant must be a formula. */
        protected JTerm parseInvariant(LocationVariable heap) {
            String string = invariants.get(index)[INV_IDX].get(heap.toString());
            JTerm result = parser.parseExpression(string);
            if (result.sort() != JavaDLTheory.FORMULA) {
                throw newUnexpectedTypeException(JavaDLTheory.FORMULA, result.sort());
            }
            return result;
        }

        /** Swing {@code parseModifiable}: the modifiable clause must be a locset. */
        protected JTerm parseModifiable(LocationVariable heap) {
            Sort locSetSort = services.getTypeConverter().getLocSetLDT().targetSort();
            String string = invariants.get(index)[MOD_IDX].get(heap.toString());
            if (string.trim().equals("\\strictly_nothing")) {
                // the Swing hack to allow "strictly_nothing" in interactive mode (:992-997)
                return services.getTermBuilder().strictlyNothing();
            }
            JTerm result = parser.parseExpression(string);
            if (result.sort() != locSetSort) {
                throw newUnexpectedTypeException(locSetSort, result.sort());
            }
            return result;
        }

        /** Swing {@code parseInfFlowSpec} (base heap only). */
        protected ImmutableList<InfFlowSpec> parseInfFlowSpec(LocationVariable heap) {
            String preExpsAsString = invariants.get(index)[IF_PRE_IDX].get(heap.toString());
            String postExpsAsString = invariants.get(index)[IF_POST_IDX].get(heap.toString());
            String newObjectsAsString = invariants.get(index)[IF_OO_IDX].get(heap.toString());
            JTerm preExps = parser.parseExpression(preExpsAsString);
            JTerm postExps = parser.parseExpression(postExpsAsString);
            JTerm newObjects = parser.parseExpression(newObjectsAsString);
            return ImmutableList.<InfFlowSpec>nil()
                    .append(new InfFlowSpec(
                        ImmutableList.<JTerm>nil().append(preExps),
                        ImmutableList.<JTerm>nil().append(postExps),
                        ImmutableList.<JTerm>nil().append(newObjects)));
        }

        /** Swing {@code parseVariant}: the variant must be an integer term. */
        protected JTerm parseVariant() {
            Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();
            JTerm result = parser.parseExpression(invariants.get(index)[VAR_IDX].get(DEFAULT));
            if (result.sort() != intSort) {
                throw newUnexpectedTypeException(intSort, result.sort());
            }
            return result;
        }

        /** Swing {@code parse}: parses all fields and updates the status panel. */
        private void parse() {
            Map<String, String> invErrors = new LinkedHashMap<>();
            Map<String, String> modErrors = new LinkedHashMap<>();
            Map<String, String> respErrors = new LinkedHashMap<>();
            for (LocationVariable heap : allHeaps()) {
                try {
                    invariantTerm.put(heap, parseInvariant(heap));
                    invErrors.put(heap.name().toString(), "OK");
                } catch (Exception e) {
                    invErrors.put(heap.name().toString(), e.getMessage());
                }
                try {
                    modifiableTerm.put(heap, parseModifiable(heap));
                    modErrors.put(heap.name().toString(), "OK");
                } catch (Exception e) {
                    modErrors.put(heap.name().toString(), e.getMessage());
                }
            }
            LocationVariable baseHeap = baseHeap();
            try {
                infFlowSpecs.put(baseHeap, parseInfFlowSpec(baseHeap));
                respErrors.put(baseHeap.name().toString(), "OK");
            } catch (Exception e) {
                respErrors.put(baseHeap.name().toString(), e.getMessage());
            }
            String varError = null;
            boolean varEvaluated = false;
            try {
                if (invariants.get(index)[VAR_IDX].get(DEFAULT).isEmpty()) {
                    variantTerm = null;
                    if (requiresVariant) {
                        throw new de.uka.ilkd.key.parser.ParserException("Variant required!",
                            null);
                    }
                    // Swing: the empty variant without requirement leaves the status unchanged
                    varEvaluated = variantStatus.getText() != null
                            && !variantStatus.getText().isEmpty();
                } else {
                    variantTerm = parseVariant();
                    varError = "OK";
                    varEvaluated = true;
                }
            } catch (Exception e) {
                varError = e.getMessage();
                varEvaluated = true;
            }

            updateStatuses(invErrors, modErrors, varEvaluated ? varError : null);
        }

        /**
         * Swing {@code updateErrorPanel}: the per-heap status texts and Apply/Store enablement.
         * A {@code null} {@code varError} leaves the variant status unchanged (the Swing
         * behaviour for the empty non-required variant).
         */
        private void updateStatuses(Map<String, String> invErrors,
                Map<String, String> modErrors, String varError) {
            boolean errorFound = false;
            for (Map.Entry<String, TextArea> entry : invariantStatus.entrySet()) {
                String error = invErrors.getOrDefault(entry.getKey(), "OK");
                errorFound |= !"OK".equals(error);
                setStatus(entry.getValue(), error);
            }
            for (Map.Entry<String, TextArea> entry : modifiableStatus.entrySet()) {
                String error = modErrors.getOrDefault(entry.getKey(), "OK");
                errorFound |= !"OK".equals(error);
                setStatus(entry.getValue(), error);
            }
            if (varError != null) {
                errorFound |= !"OK".equals(varError);
                setStatus(variantStatus, varError);
            } else {
                String current = variantStatus.getText();
                errorFound |= current != null && !current.isEmpty() && !"OK".equals(current);
            }
            // Swing: applyButton.setEnabled(!errorFound); storeButton likewise (:946-948)
            applyButton.setDisable(errorFound);
            storeButton.setDisable(errorFound);
        }

        private void setStatus(TextArea area, String message) {
            area.getStyleClass().removeAll(List.of("invariant-status-ok",
                "invariant-status-error"));
            area.getStyleClass()
                    .add("OK".equals(message) ? "invariant-status-ok" : "invariant-status-error");
            area.setText(message);
        }

        /** Swing {@code buildInvariant}: builds the new invariant if the requirements are met. */
        private boolean buildInvariant() {
            boolean requirementsAreMet = true;
            if (requiresVariant && variantTerm == null) {
                setStatus(variantStatus, "Variant required!");
                requirementsAreMet = false;
            }
            if (invariantTerm.isEmpty()) {
                setStatus(variantStatus, "Invariant is required!");
                requirementsAreMet = false;
            }
            if (requirementsAreMet) {
                newInvariant = loopInv.configurate(invariantTerm, freeInvariantTerm,
                    modifiableTerm, freeModifiableTerm, infFlowSpecs, variantTerm);
                return true;
            }
            return false;
        }

        // ------------------------------------------------------------------
        // actions (Swing apply/store/cancel, :769-788)
        // ------------------------------------------------------------------

        /** Swing {@code applyActionPerformed}: parse, build, close on success. */
        private void applyActionPerformed() {
            index = inputPane.getSelectionModel().getSelectedIndex();
            parse();
            if (buildInvariant()) {
                stage.close();
            }
        }

        /** Swing {@code storeActionPerformed}: clone the current candidate into a new tab. */
        @SuppressWarnings("unchecked")
        private void storeActionPerformed() {
            index = inputPane.getSelectionModel().getSelectedIndex();
            // Swing shallow-clones the array (the candidate maps are shared, as in Swing)
            Map<String, String>[] invs = invariants.get(index).clone();
            invariants.add(invs);
            index = invariants.size() - 1;
            inputPane.getTabs().add(new Tab("Inv " + (invariants.size() - 1),
                createInvariantTab(index)));
            inputPane.getSelectionModel().select(index);
        }

        /** Swing {@code cancelActionPerformed}. */
        private void cancelActionPerformed() {
            userPressedCancel = true;
            newInvariant = null;
            stage.close();
        }

        // ------------------------------------------------------------------
        // display
        // ------------------------------------------------------------------

        /** Shows the dialog modally (blocks until closed). */
        private void show() {
            if (!FxUtil.isFxThread()) {
                FxUtil.runLater(this::show);
                return;
            }
            stage.initModality(Modality.APPLICATION_MODAL);
            stage.showAndWait();
        }
    }
}
