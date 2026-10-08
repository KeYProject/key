/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.proofmanagement;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Consumer;
import java.util.stream.Stream;
import javafx.concurrent.Task;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Window;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.ast.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofStatus;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The JavaFX proof management dialog, counter-part of {@code de.uka.ilkd.key.gui.
 * ProofManagementDialog} (key.ui, ProofManagementDialog.java:52-681). The dialog shows the
 * contracts of the loaded Java classpath and starts or navigates to the proof of the selected
 * contract:
 * <ul>
 * <li><b>By Target</b> tab: the {@link ClassTreeF} (the ported Swing {@code ClassTree}) of the
 * classpath types and their contract targets, each target leaf annotated with the proof status of
 * its non-auxiliary contracts (the {@code targetIcons} computation,
 * ProofManagementDialog.java:565-617), and a {@link ContractSelectionPanelF} with the contracts of
 * the selected target (ProofManagementDialog.java:540-552);</li>
 * <li><b>By Proof</b> tab: the list of all proofs registered with the specification repository,
 * newest first (ProofManagementDialog.java:620-640), with the contracts used in the selected proof
 * (ProofManagementDialog.java:553-557);</li>
 * <li><b>Start Proof</b> / <b>Go to Proof</b> and <b>Cancel</b> buttons with the Swing enablement
 * ({@code updateStartButton}, ProofManagementDialog.java:502-530) and load semantics
 * ({@code findOrStartProof}, ProofManagementDialog.java:466-500): an existing proof for the
 * selected contract is activated ("Go to Proof"), otherwise a new proof is created via the core
 * {@link ProblemInitializer} on a background thread and registered in the proof environment;</li>
 * <li>double-click shortcuts on tree targets with exactly one contract, contract panels and proof
 * rows (ProofManagementDialog.java:91-113, 169-190);</li>
 * <li>the last contract is remembered across dialog invocations
 * ({@code previouslySelectedContracts}, ProofManagementDialog.java:59-61, 343-345, 364-370).</li>
 * </ul>
 * <p>
 * Deliberate deviations from the Swing original: the auxiliary-contract graying of
 * {@code ContractSelectionPanel} is not ported (needs the closed-proof/used-contract fixpoint),
 * the {@code mediator.startInterface(true)} call (ProofManagementDialog.java:497-499) has no FX
 * counterpart (the FX mediator is always interactive), and proof starting runs on a background
 * thread ({@link Task}) instead of the EDT.
 * <p>
 * <b>proofmgmt: TODO-merge hook into WindowUserInterfaceControlF load flow</b> — currently
 * standalone: the caller hands in the {@link DefaultUserInterfaceControl} of the environment the
 * problem was loaded with (MainWindowF keeps the most recent one). Once
 * {@code WindowUserInterfaceControlF} exists: (a) pass {@code mediator.getUI()} instead (Swing
 * ProofManagementDialog.java:469), (b) let
 * {@code WindowUserInterfaceControlF.selectProofObligation}
 * (counterpart of {@code WindowUserInterfaceControl.java:516}) call {@link #showInstance} so bare
 * {@code .java} loads route into this dialog, and (c) route {@code registerProofAggregate} of the
 * proofs started here into the {@code ProofManagerF} of the Loaded Proofs view (the
 * {@code proofSelector} callback of this dialog is the seam).
 */
public final class ProofManagementDialogF {

    private static final Logger LOGGER = LoggerFactory.getLogger(ProofManagementDialogF.class);

    /**
     * The visual proof status (Swing key-hole icons of the renderers in TaskTree.java:348-394 and
     * ProofManagementDialog.java:118-145, expressed as CSS-colored font icons). Shared with the
     * Loaded Proofs view ({@code TaskTreeF}).
     */
    public enum StatusKind {
        /** open proof (Swing key-hole icon {@code keyHole}). */
        OPEN("proof-status-open", "Open proof"),
        /** closed proof (Swing {@code keyHoleClosed}). */
        CLOSED("proof-status-closed", "Closed proof"),
        /**
         * closed proof that still depends on other contracts (Swing
         * {@code keyHoleAlmostClosed}).
         */
        ALMOST_CLOSED("proof-status-almost-closed",
                "Closed proof (depends on other contracts)"),
        /** closed proof via the proof cache (Swing {@code keyCachedClosed}). */
        CLOSED_BY_CACHE("proof-status-closed-cache", "Closed proof (using proof cache)"),
        /** no status (not shown). */
        NONE(null, null);

        private final @Nullable String styleClass;
        private final @Nullable String tooltip;

        StatusKind(@Nullable String styleClass, @Nullable String tooltip) {
            this.styleClass = styleClass;
            this.tooltip = tooltip;
        }

        /**
         * Maps a {@link ProofStatus} onto the visual state; the precedence mirrors the Swing
         * renderer (TaskTree.java:373-389: almost closed / cache / closed / open).
         */
        public static StatusKind fromProofStatus(@Nullable ProofStatus ps) {
            if (ps == null) {
                return NONE;
            }
            if (ps.getProofClosedButLemmasLeft()) {
                return ALMOST_CLOSED;
            } else if (ps.getProofClosedByCache()) {
                return CLOSED_BY_CACHE;
            } else if (ps.getProofClosed()) {
                return CLOSED;
            } else {
                return OPEN;
            }
        }

        /** @return the CSS style class coloring the status icon, {@code null} = not shown */
        public @Nullable String styleClass() {
            return styleClass;
        }

        /** @return the tooltip describing the status, {@code null} = no tooltip */
        public @Nullable String tooltip() {
            return tooltip;
        }
    }

    /**
     * The last contract for which a proof was started or selected, stored by type name, method
     * name, and contract name to avoid keeping environments alive (Swing
     * {@code previouslySelectedContracts}, ProofManagementDialog.java:57-61).
     */
    private static @Nullable ContractId previouslySelectedContracts;

    /** the dialog window (Swing JDialog, :52). */
    private final javafx.stage.Stage stage = new javafx.stage.Stage();
    /** the initial configuration of the loaded problem (Swing {@code initConfig}, :77). */
    private final InitConfig initConfig;
    /** the services of {@link #initConfig}. */
    private final Services services;
    /**
     * The user interface control proofs are started with (Swing uses {@code mediator.getUI()},
     * ProofManagementDialog.java:469). The caller passes the control of the environment the
     * problem was loaded with — the TODO-merge seam noted in the class javadoc.
     */
    private final DefaultUserInterfaceControl ui;
    /**
     * activates a proof in the main window (the Swing dialog calls
     * {@code mediator.getSelectionModel().setSelectedProof}, ProofManagementDialog.java:486, :492).
     */
    private final Consumer<Proof> proofSelector;

    /** the target tree of the "By Target" tab (Swing {@code classTree}, :70). */
    private final ClassTreeF classTree;
    /** the proof status per target leaf (Swing {@code targetIcons}, :69). */
    private final Map<ClassTreeF.Entry, StatusKind> targetIcons = new LinkedHashMap<>();
    /** the proof list of the "By Proof" tab (Swing {@code proofList}, :71). */
    private final ListView<Proof> proofList = new ListView<>();
    /** the contract panel of the "By Target" tab (Swing {@code contractPanelByMethod}, :72). */
    private final ContractSelectionPanelF contractPanelByMethod;
    /** the contract panel of the "By Proof" tab (Swing {@code contractPanelByProof}, :73). */
    private final ContractSelectionPanelF contractPanelByProof;
    /** the tabs (Swing {@code tabbedPane}, :68). */
    private final TabPane tabbedPane = new TabPane();
    /** the "Start Proof"/"Go to Proof" button (Swing {@code startButton}, :74). */
    private final Button startButton = new Button();
    /** whether a proof was started or selected during this dialog invocation (:67). */
    private boolean startedProof;

    /**
     * The proof environment to register started proofs in (Swing {@code env}, :78): the
     * environment of the selected proof, or {@code null} (a new environment is created then).
     */
    private @Nullable ProofEnvironment env;

    /**
     * Creates and lays out the dialog (Swing constructor, ProofManagementDialog.java:83-240).
     *
     * @param owner the owner window (the main window stage), may be {@code null}
     * @param initConfig the initial configuration of the loaded problem
     * @param ui the user interface control proofs are started with
     * @param proofSelector called with the proof to activate in the main window
     * @param selectedProof the proof to preselect on the "By Proof" tab, may be {@code null}
     */
    public ProofManagementDialogF(@Nullable Window owner, InitConfig initConfig,
            DefaultUserInterfaceControl ui, Consumer<Proof> proofSelector,
            @Nullable Proof selectedProof) {
        this.initConfig = initConfig;
        this.services = initConfig.getServices();
        this.ui = ui;
        this.proofSelector = proofSelector;
        if (selectedProof != null) {
            this.env = selectedProof.getEnv();
        }

        stage.setTitle("Proof Management");
        stage.initModality(Modality.WINDOW_MODAL);
        if (owner != null) {
            stage.initOwner(owner);
        }

        contractPanelByMethod =
            new ContractSelectionPanelF(services, (obs, oldV, newV) -> updateStartButton());
        contractPanelByProof =
            new ContractSelectionPanelF(services, (obs, oldV, newV) -> updateStartButton());

        // --- "By Target" tab: class tree + contract panel ---------------------
        // create class tree (ProofManagementDialog.java:88-90); the target status icons are
        // computed in updateGlobalStatus
        classTree = new ClassTreeF(true, true, services);
        classTree.setCellFactory(view -> new javafx.scene.control.TreeCell<ClassTreeF.Entry>() {
            @Override
            protected void updateItem(ClassTreeF.Entry item, boolean empty) {
                super.updateItem(item, empty);
                if (empty || item == null) {
                    setText(null);
                    setGraphic(null);
                    setTooltip(null);
                    return;
                }
                setText(item.string);
                setStyle(item.target == null ? "-fx-font-weight: bold;" : null);
                StatusKind kind = targetIcons.get(item);
                if (kind != null && kind.styleClass() != null) {
                    var icon = IconFactoryF.createIcon(IconFactoryF.Key.KEY_HOLE, 14);
                    icon.getStyleClass().add(kind.styleClass());
                    setGraphic(icon);
                    setTooltip(new Tooltip(kind.tooltip()));
                } else {
                    setGraphic(null);
                    setTooltip(null);
                }
            }
        });
        // selection refreshes the contract panel (ProofManagementDialog.java:114)
        classTree.getSelectionModel().selectedItemProperty()
                .addListener((obs, oldV, item) -> updateContractPanel());
        // double click on a target with exactly one contract starts the proof
        // (ProofManagementDialog.java:91-113)
        classTree.setOnMouseClicked(e -> {
            if (e.getClickCount() == 2) {
                ClassTreeF.Entry entry = classTree.getSelectedEntry();
                if (entry != null && entry.kjt != null && entry.target != null) {
                    ImmutableSet<Contract> contracts =
                        services.getSpecificationRepository().getContracts(entry.kjt, entry.target);
                    Contract c = contracts.isEmpty() ? null : contracts.iterator().next();
                    if (contracts.size() == 1 && c == contractPanelByMethod.getContract()) {
                        startSelectedContract();
                    }
                }
            }
        });

        // --- "By Proof" tab: proof list + contract panel ----------------------
        // the proof list renderer (ProofManagementDialog.java:118-145): the proof name with the
        // proof status icon
        proofList.setCellFactory(view -> new ListCell<>() {
            @Override
            protected void updateItem(Proof item, boolean empty) {
                super.updateItem(item, empty);
                if (empty || item == null) {
                    setText(null);
                    setGraphic(null);
                    setTooltip(null);
                } else {
                    setText(item.name().toString());
                    StatusKind kind = StatusKind.fromProofStatus(item.mgt().getStatus());
                    if (kind.styleClass() != null) {
                        var icon = IconFactoryF.createIcon(IconFactoryF.Key.KEY_HOLE, 14);
                        icon.getStyleClass().add(kind.styleClass());
                        setGraphic(icon);
                        setTooltip(new Tooltip(kind.tooltip()));
                    } else {
                        setGraphic(null);
                        setTooltip(null);
                    }
                }
            }
        });
        // selection refreshes the contract panel (ProofManagementDialog.java:146)
        proofList.getSelectionModel().selectedItemProperty()
                .addListener((obs, oldV, proof) -> updateContractPanel());
        // double click on a proof row starts the proof of the selected contract (:182-190)
        proofList.setOnMouseClicked(e -> {
            if (e.getClickCount() == 2) {
                startSelectedContract();
            }
        });

        // --- tabs + buttons ---------------------------------------------------
        Tab byTarget = new Tab("By Target", buildTabContent(classTree, contractPanelByMethod));
        byTarget.setClosable(false);
        Tab byProof = new Tab("By Proof", buildTabContent(proofList, contractPanelByProof));
        byProof.setClosable(false);
        tabbedPane.getTabs().addAll(byTarget, byProof);
        // tab change updates the start button and preselects the first proof
        // (ProofManagementDialog.java:198-203)
        tabbedPane.getSelectionModel().selectedItemProperty().addListener((obs, oldV, tab) -> {
            updateStartButton();
            if (proofList.getSelectionModel().isEmpty() && !proofList.getItems().isEmpty()) {
                proofList.getSelectionModel().selectFirst();
            }
        });

        startButton.setPrefWidth(140);
        startButton.setDisable(true);
        startButton.setOnAction(e -> startSelectedContract());
        Button cancelButton = new Button("Cancel");
        cancelButton.setPrefWidth(140);
        cancelButton.setCancelButton(true);
        cancelButton.setOnAction(e -> stage.close());
        Region spacer = new Region();
        HBox.setHgrow(spacer, Priority.ALWAYS);
        HBox buttonPanel = new HBox(5, spacer, startButton, cancelButton);
        buttonPanel.setAlignment(Pos.CENTER_RIGHT);
        buttonPanel.setPadding(new Insets(8, 8, 8, 8));

        BorderPane root = new BorderPane();
        root.setCenter(tabbedPane);
        root.setBottom(buttonPanel);

        Scene scene = new Scene(root, 950, 620);
        ThemeManager.getInstance().style(scene);
        stage.setScene(scene);
    }

    /**
     * Builds one tab's content: the selection list on the left, the contract panel on the right
     * (Swing BoxLayout list panels, ProofManagementDialog.java:149-192).
     */
    private BorderPane buildTabContent(javafx.scene.control.Control list,
            ContractSelectionPanelF contractPanel) {
        BorderPane pane = new BorderPane();
        pane.setPadding(new Insets(8));
        Label heading = new Label(list == proofList ? "Proofs" : "Contract Targets");
        heading.getStyleClass().add("dialog-section-title");
        VBox left = new VBox(2, heading, list);
        VBox.setVgrow(list, Priority.ALWAYS);
        left.setPrefWidth(330);
        pane.setCenter(left);
        pane.setRight(contractPanel);
        BorderPane.setMargin(contractPanel, new Insets(0, 0, 0, 8));
        return pane;
    }

    // ------------------------------------------------------------------
    // status computation
    // ------------------------------------------------------------------

    /**
     * Computes the status icons of all contract targets and fills the proof list (ProofManagement
     * Dialog.{@code updateGlobalStatus}, :565-645).
     */
    private void updateGlobalStatus() {
        // target icons (:565-617)
        targetIcons.clear();
        SpecificationRepository specRepos = services.getSpecificationRepository();
        var kjts = services.getJavaInfo().getAllKeYJavaTypes();
        for (KeYJavaType kjt : kjts) {
            // skip library classes, the user isn't shown contracts for them
            if (kjt.getJavaType() instanceof TypeDeclaration
                    && ((TypeDeclaration) kjt.getJavaType()).isLibraryClass()) {
                continue;
            }
            ImmutableSet<IObserverFunction> targets = specRepos.getContractTargets(kjt);
            for (IObserverFunction target : targets) {
                if (isInstanceMethodOfAbstractClass(kjt, target)) {
                    continue;
                }
                targetIcons.put(findTargetEntry(kjt, target),
                    computeTargetStatus(kjt, target, specRepos));
            }
        }
        classTree.refresh();

        // proof list: all proofs, newest first (:620-640)
        List<Proof> proofs = new ArrayList<>();
        for (Proof p : specRepos.getAllProofs()) {
            proofs.add(0, p);
        }
        proofList.getItems().setAll(proofs);
    }

    /** @return the tree leaf entry of the given type/target, or a fresh dummy entry. */
    private ClassTreeF.Entry findTargetEntry(KeYJavaType kjt, IObserverFunction target) {
        ClassTreeF.Entry entry = searchTargetEntry(classTree.getRootNode(), kjt, target);
        return entry != null ? entry : new ClassTreeF.Entry("");
    }

    /** depth-first search for the leaf entry with the given type/target. */
    private static ClassTreeF.@Nullable Entry searchTargetEntry(
            javafx.scene.control.TreeItem<ClassTreeF.Entry> item, KeYJavaType kjt,
            IObserverFunction target) {
        ClassTreeF.Entry value = item.getValue();
        if (value.target != null && target.equals(value.target) && kjt.equals(value.kjt)) {
            return value;
        }
        for (javafx.scene.control.TreeItem<ClassTreeF.Entry> child : item.getChildren()) {
            ClassTreeF.Entry found = searchTargetEntry(child, kjt, target);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    /**
     * Computes the status icon of one contract target (ProofManagementDialog.java:581-614): the
     * aggregate over the non-auxiliary contracts, "not started" (no icon) if no contract has a
     * proof.
     */
    private StatusKind computeTargetStatus(KeYJavaType kjt, IObserverFunction target,
            SpecificationRepository specRepos) {
        boolean startedProving = false;
        boolean allClosed = true;
        boolean lemmasLeft = false;
        boolean cached = false;
        for (Contract contract : specRepos.getContracts(kjt, target)) {
            // skip auxiliary contracts like block/loop contracts (ProofManagementDialog.java:588)
            if (contract.isAuxiliary()) {
                continue;
            }
            Proof proof = findPreferablyClosedProof(contract);
            if (proof == null) {
                allClosed = false;
            } else {
                startedProving = true;
                ProofStatus status = proof.mgt().getStatus();
                if (status.getProofOpen()) {
                    allClosed = false;
                } else if (status.getProofClosedButLemmasLeft()) {
                    lemmasLeft = true;
                }
                if (status.getProofClosedByCache()) {
                    cached = true;
                }
            }
        }
        if (!startedProving) {
            return StatusKind.NONE;
        }
        if (!allClosed) {
            return StatusKind.OPEN;
        }
        if (cached) {
            return StatusKind.CLOSED_BY_CACHE;
        }
        return lemmasLeft ? StatusKind.ALMOST_CLOSED : StatusKind.CLOSED;
    }

    /**
     * Finds a proof for the given contract, preferring a closed proof, then one that just misses
     * lemmas (ProofManagementDialog.findPreferablyClosedProof, :444-464).
     *
     * @return the proof or {@code null} if there is no proof for the contract
     */
    private @Nullable Proof findPreferablyClosedProof(@NonNull Contract contract) {
        ImmutableSet<Proof> proofs = services.getSpecificationRepository().getProofs(contract);
        if (proofs.isEmpty()) {
            return null;
        }
        Proof fallback = null;
        for (Proof proof : proofs) {
            final ProofStatus status = proof.mgt().getStatus();
            if (status.getProofClosed()) {
                return proof;
            } else if (fallback == null || status.getProofClosedButLemmasLeft()) {
                fallback = proof;
            }
        }
        return fallback;
    }

    /** Swing {@code ProofManagementDialog.isInstanceMethodOfAbstractClass}, :533-536. */
    private static boolean isInstanceMethodOfAbstractClass(KeYJavaType kjt,
            IObserverFunction obs) {
        return kjt.getJavaType() instanceof InterfaceDeclaration
                || (kjt.getSort().isAbstract() && !obs.isStatic());
    }

    /** the target sort order of ProofManagementDialog.java:273-287 (ClassTree.java:157-172). */
    private static Comparator<IObserverFunction> targetComparator() {
        return (o1, o2) -> {
            if (o1 instanceof IProgramMethod && !(o2 instanceof IProgramMethod)) {
                return -1;
            } else if (!(o1 instanceof IProgramMethod) && o2 instanceof IProgramMethod) {
                return 1;
            }
            return targetSortName(o1).compareTo(targetSortName(o2));
        };
    }

    private static String targetSortName(IObserverFunction o) {
        return o.name() instanceof ProgramElementName
                ? ((ProgramElementName) o.name()).getProgramName()
                : o.name().toString();
    }

    // ------------------------------------------------------------------
    // selection / panel updates
    // ------------------------------------------------------------------

    /**
     * Refreshes the contract panel of the active tab (ProofManagementDialog.
     * {@code updateContractPanel}, :538-563).
     */
    private void updateContractPanel() {
        if (isByTargetTab()) {
            ClassTreeF.Entry entry = classTree.getSelectedEntry();
            if (entry != null && entry.target != null
                    && !isInstanceMethodOfAbstractClass(entry.kjt, entry.target)) {
                ImmutableSet<Contract> contracts =
                    services.getSpecificationRepository().getContracts(entry.kjt, entry.target);
                contractPanelByMethod.setContracts(contracts, "Contracts");
                // auxiliary contracts are grayed out if the target's proof is already closed
                // (ProofManagementDialog.java:548-549) — not ported, see the class javadoc
            } else {
                contractPanelByMethod.setContracts(DefaultImmutableSet.nil(), "Contracts");
            }
        } else {
            Proof proof = proofList.getSelectionModel().getSelectedItem();
            if (proof != null) {
                contractPanelByProof.setContracts(proof.mgt().getUsedContracts(),
                    "Contracts used in proof \"" + proof.name() + "\"");
            } else {
                contractPanelByProof.setContracts(DefaultImmutableSet.nil(), "Contracts");
            }
        }
        updateStartButton();
    }

    /**
     * Updates the start button text and enablement (ProofManagementDialog.
     * {@code updateStartButton}, :502-530): "No Contract" (disabled) / "Start Proof" / "Go to
     * Proof" (a proof for the selected contract already exists).
     */
    private void updateStartButton() {
        Contract contract = getSelectedContract();
        if (contract == null) {
            startButton.setText("No Contract");
            startButton.setDisable(true);
        } else {
            Proof proof = findPreferablyClosedProof(contract);
            startButton.setText(proof == null ? "Start Proof" : "Go to Proof");
            startButton.setDisable(false);
        }
    }

    /** @return the contract of the active tab's panel (Swing {@code getSelectedContract}, :432). */
    private @Nullable Contract getSelectedContract() {
        return isByTargetTab() ? contractPanelByMethod.getContract()
                : contractPanelByProof.getContract();
    }

    private boolean isByTargetTab() {
        return tabbedPane.getSelectionModel().getSelectedIndex() == 0;
    }

    // ------------------------------------------------------------------
    // start proof
    // ------------------------------------------------------------------

    /**
     * The start button action (ProofManagementDialog.java:219-225): hides the dialog and starts
     * or selects the proof of the selected contract.
     */
    private void startSelectedContract() {
        Contract contract = getSelectedContract();
        if (contract == null) {
            return;
        }
        stage.close();
        findOrStartProof(contract);
    }

    /**
     * Starts or selects the proof for the given contract (ProofManagementDialog.
     * {@code findOrStartProof}, :466-500): an existing proof is activated in the main window;
     * otherwise a new proof is created with the core {@link ProblemInitializer} on a background
     * thread and registered in the proof environment.
     * <p>
     * proofmgmt: TODO-merge hook into WindowUserInterfaceControlF load flow — the Swing dialog
     * uses {@code mediator.getUI()} here (ProofManagementDialog.java:469); the standalone port
     * uses the environment's UI control handed in by the caller. Merge: route through
     * {@code WindowUserInterfaceControlF} and report the new proof aggregate to the
     * {@code ProofManagerF} of the Loaded Proofs view.
     */
    private void findOrStartProof(@NonNull Contract contract) {
        Proof proof = findPreferablyClosedProof(contract);
        if (proof != null) {
            proofSelector.accept(proof);
            startedProof = true;
            rememberSelectedContract(contract);
            return;
        }

        Task<Proof> startTask = new Task<>() {
            @Override
            protected Proof call() throws Exception {
                ProblemInitializer pi = new ProblemInitializer(ui, services, ui);
                // enables to access the FileRepo created in AbstractProblemLoader
                // (ProofManagementDialog.java:473-474)
                pi.setFileRepo(initConfig.getFileRepo());
                ProofOblInput po =
                    contract.createProofObl(initConfig.copyWithServices(initConfig.getServices()));
                ProofAggregate pl = pi.startProver(initConfig, po);

                // register the new proof in the environment of the selected proof, or in a fresh
                // one (ProofManagementDialog.java:481-485)
                if (env == null) {
                    env = ui.createProofEnvironmentAndRegisterProof(po, pl, initConfig);
                } else {
                    env.registerProof(po, pl);
                }
                return pl.getFirstProof();
            }
        };
        startTask.setOnSucceeded(event -> {
            Proof newProof = startTask.getValue();
            LOGGER.info("Proof management: started proof for contract {}", contract.getName());
            NotificationManagerF.getInstance()
                    .notify("Started proof for contract " + contract.getName(), Kind.INFO);
            proofSelector.accept(newProof);
        });
        startTask.setOnFailed(event -> {
            Throwable error = startTask.getException();
            LOGGER.error("Proof management: starting proof for contract " + contract.getName()
                + " failed", error);
            NotificationManagerF.getInstance()
                    .notify("Starting proof for contract " + contract.getName()
                        + " failed: " + error.getMessage(), Kind.ERROR);
        });
        Thread worker = new Thread(startTask, "fx-proofmgmt-contract-prover");
        worker.setDaemon(true);
        worker.start();
        startedProof = true;
        rememberSelectedContract(contract);
    }

    /** Stores the started contract (ProofManagementDialog.java:364-370). */
    private void rememberSelectedContract(Contract contract) {
        previouslySelectedContracts = new ContractId(contract.getKJT().getFullName(),
            contract.getTarget().name().toString(), contract.getName());
    }

    // ------------------------------------------------------------------
    // defaults & selection before showing
    // ------------------------------------------------------------------

    /**
     * Selects the first contract of the first type sorted by name (ProofManagementDialog.
     * {@code selectKJTandTarget}, :262-301).
     */
    private void selectKJTandTarget() {
        List<KeYJavaType> allJavaTypes = services.getJavaInfo().getAllKeYJavaTypes().stream()
                .sorted(Comparator.comparing(KeYJavaType::getFullName))
                .filter(kjtTmp -> !(kjtTmp.getJavaType() instanceof TypeDeclaration
                        && ((TypeDeclaration) kjtTmp.getJavaType()).isLibraryClass()))
                .toList();
        for (KeYJavaType javaType : allJavaTypes) {
            Stream<IObserverFunction> targets = services.getSpecificationRepository()
                    .getContractTargets(javaType).stream().sorted(targetComparator())
                    .filter(targetTmp -> !services.getSpecificationRepository()
                            .getContracts(javaType, targetTmp).isEmpty());
            Optional<IObserverFunction> t = targets.findFirst();
            if (t.isPresent()) {
                select(javaType, t.get());
                break;
            }
        }
    }

    /**
     * Selects the given type/target on the "By Target" tab (ProofManagementDialog.java:415-420).
     */
    private void select(KeYJavaType kjt, IObserverFunction target) {
        tabbedPane.getSelectionModel().select(0);
        classTree.select(kjt, target);
    }

    /**
     * Selects the given proof on the "By Proof" tab (ProofManagementDialog.java:422-430).
     */
    private void select(Proof proof) {
        for (int i = 0, n = proofList.getItems().size(); i < n; i++) {
            if (proofList.getItems().get(i).equals(proof)) {
                tabbedPane.getSelectionModel().select(1);
                proofList.getSelectionModel().select(i);
                break;
            }
        }
    }

    /**
     * Selects the remembered contract (ProofManagementDialog.{@code select(ContractId)},
     * :377-409); no-op if the contract is no longer present.
     */
    private void selectPreviouslySelectedContract() {
        ContractId cid = previouslySelectedContracts;
        if (cid == null) {
            return;
        }
        Optional<KeYJavaType> kjt = services.getJavaInfo().getAllKeYJavaTypes().stream()
                .filter(it -> it.getFullName().equals(cid.keyJavaTypeName)).findAny();
        if (kjt.isEmpty()) {
            return;
        }
        Optional<IObserverFunction> target = services.getSpecificationRepository()
                .getContractTargets(kjt.get()).stream()
                .filter(it -> it.name().toString().equals(cid.methodName)).findAny();
        if (target.isEmpty()) {
            return;
        }
        select(kjt.get(), target.get());
        if (!isInstanceMethodOfAbstractClass(kjt.get(), target.get())) {
            services.getSpecificationRepository().getContracts(kjt.get(), target.get()).stream()
                    .filter(it -> it.getName().equals(cid.contractName)).findAny()
                    .ifPresent(contractPanelByMethod::selectContractAndNotify);
        }
    }

    // ------------------------------------------------------------------
    // showing
    // ------------------------------------------------------------------

    /** Fills the lists and applies the defaults before the dialog becomes visible. */
    private void prepareAndShow() {
        updateGlobalStatus();
        // determine own defaults if not given (ProofManagementDialog.java:341-346)
        selectKJTandTarget();
        selectPreviouslySelectedContract();
        updateContractPanel();
        updateStartButton();
    }

    /**
     * Fills the lists and opens the dialog modally (ProofManagementDialog.
     * {@code showInstance}, :336-372).
     *
     * @return {@code true} if a proof was started or selected
     */
    public boolean showAndWaitInstance() {
        prepareAndShow();
        stage.showAndWait();
        return startedProof;
    }

    /**
     * Fills the lists and shows the dialog <em>without</em> blocking (the self test shows the
     * dialog, inspects it and closes it; Swing {@code setVisible(true)}).
     */
    public void showForVerification() {
        prepareAndShow();
        stage.show();
    }

    /** Closes the dialog (Swing {@code setVisible(false)}, ProofManagementDialog.java:233). */
    public void close() {
        stage.close();
    }

    // ------------------------------------------------------------------
    // static entry points
    // ------------------------------------------------------------------

    /**
     * Shows the dialog modally and returns whether a proof was started or selected (Swing
     * {@code ProofManagementDialog.showInstance(InitConfig, Proof)},
     * ProofManagementDialog.java:306-308, 336-372).
     *
     * @param owner the owner window (the main window stage), may be {@code null}
     * @param initConfig the initial configuration of the loaded problem
     * @param ui the user interface control proofs are started with
     * @param proofSelector called with the proof to activate in the main window
     * @param selectedProof the proof to preselect, may be {@code null}
     */
    public static boolean showInstance(@Nullable Window owner, InitConfig initConfig,
            DefaultUserInterfaceControl ui, Consumer<Proof> proofSelector,
            @Nullable Proof selectedProof) {
        ProofManagementDialogF dialog =
            new ProofManagementDialogF(owner, initConfig, ui, proofSelector, selectedProof);
        return dialog.showAndWaitInstance();
    }

    /**
     * Creates a dialog for the self test ({@code key.fx.verify.proofmgmt}): the caller inspects
     * it with {@link #verifyDialog()} and shows it with {@link #showForVerification()}.
     */
    public static ProofManagementDialogF createForVerification(@Nullable Window owner,
            InitConfig initConfig, DefaultUserInterfaceControl ui,
            Consumer<Proof> proofSelector) {
        return new ProofManagementDialogF(owner, initConfig, ui, proofSelector, null);
    }

    // ------------------------------------------------------------------
    // self test support
    // ------------------------------------------------------------------

    /**
     * Runs the structural self test of the filled dialog: the "By Target" tree contains the
     * contract targets with statuses, the "By Proof" list contains all proofs, a contract is
     * selected and the start button enabled. Logging is left to the caller. Must be called after
     * {@link #showForVerification()} (or the internal {@code prepareAndShow}).
     *
     * @return a report string ending in PASS or FAIL
     */
    public String verifyDialog() {
        var checks = new ArrayList<String>();
        long targets = targetIcons.size();
        long targetsWithProof = targetIcons.values().stream().filter(k -> k != StatusKind.NONE)
                .count();
        check(checks, "target tree has " + targets + " contract target(s)", targets > 0);
        check(checks, targetsWithProof + " target(s) with a proof status",
            targetsWithProof > 0);
        check(checks, "proof list shows " + proofList.getItems().size() + " proof(s)",
            !proofList.getItems().isEmpty());
        Contract selected = getSelectedContract();
        check(checks, "a contract is selected (" + (selected == null ? "-" : selected.getName())
            + ")", selected != null);
        check(checks, "start button enabled", !startButton.isDisable());
        boolean ok = checks.stream().allMatch(c -> c.startsWith("PASS"));
        return String.join("; ", checks) + (ok ? " PASS" : " FAIL");
    }

    /** appends a PASS/FAIL line for one check. */
    private static void check(List<String> checks, String what, boolean ok) {
        checks.add((ok ? "PASS" : "FAIL") + " [" + what + "]");
    }

    /** Records the identification of a contract (ProofManagementDialog.java:670-681). */
    private record ContractId(String keyJavaTypeName, String methodName, String contractName) {
    }
}
