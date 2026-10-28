/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Stream;
import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
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
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofStatus;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;

import org.key_project.logic.Name;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

@NullMarked
public final class ProofManagementDialog extends JDialog {

    private static final long serialVersionUID = 3543411893273433386L;
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofManagementDialog.class);

    /**
     * The contracts are stored by name of the {@link KeYJavaType}, method name, and contract name
     * to avoid keeping environments in the memory.
     */
    private static @Nullable ContractId previouslySelectedContracts;

    private static final ImageIcon KEY_OPEN = IconFactory.keyHole(20, 20);
    private static final ImageIcon KEY_ALMOST_CLOSED = IconFactory.keyHoleAlmostClosed(20, 20);
    private static final ImageIcon KEY_CACHED_CLOSED = IconFactory.keyCachedClosed(20, 20);
    private static final Icon KEY_CLOSED = IconFactory.keyHoleClosed(20);
    private boolean startedProof;
    private @Nullable JTabbedPane tabbedPane;
    private @Nullable Map<Pair<KeYJavaType, IObserverFunction>, @Nullable Icon> targetIcons;
    private @Nullable ClassTree classTree;
    private @Nullable JList<ProofWrapper> proofList;
    private @Nullable ContractSelectionPanel contractPanelByMethod;
    private @Nullable ContractSelectionPanel contractPanelByProof;
    private @Nullable JButton startButton;
    private @Nullable JButton cancelButton;
    private final KeYMediator mediator;
    private final InitConfig initConfig;
    private @Nullable ProofEnvironment env;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------
    private ProofManagementDialog(MainWindow mainWindow, final InitConfig initConfig) {
        super(mainWindow, "Proof Management", true);
        this.mediator = mainWindow.getMediator();
        this.initConfig = initConfig;

        // create class tree
        Map<Pair<KeYJavaType, IObserverFunction>, @Nullable Icon> icons = new LinkedHashMap<>();
        ClassTree tree = new ClassTree(true, true, initConfig.getServices(), icons);
        targetIcons = icons;
        classTree = tree;
        tree.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                // Check that it is a double click on an item, not a folder or the background
                if (e.getClickCount() != 2) {
                    return;
                }
                // row is -1 when the user does not click on an entry but on the background
                int row = classTree.getRowForLocation(e.getX(), e.getY());
                if (row == -1) {
                    return;
                }
                final ClassTree.Entry entry = classTree.getSelectedEntry();
                if (entry.kjt != null && entry.target != null) {
                    final ImmutableSet<Contract> contracts = initConfig.getServices()
                            .getSpecificationRepository().getContracts(entry.kjt, entry.target);
                    final Contract c = contracts.iterator().next();
                    if (contracts.size() == 1 && c == contractPanelByMethod.getContract()) {
                        startButton.doClick();
                    }
                }
            }
        });
        tree.addTreeSelectionListener(e -> updateContractPanel());

        // create proof list
        JList<ProofWrapper> list = new JList<>();
        proofList = list;
        list.setCellRenderer(new DefaultListCellRenderer() {
            private static final long serialVersionUID = -7810888250050777877L;

            @Override
            public Component getListCellRendererComponent(JList<?> list, Object value, int index,
                    boolean isSelected, boolean cellHasFocus) {
                Component result = super.getListCellRendererComponent(list, value, index,
                    isSelected, cellHasFocus);

                if (result instanceof JLabel label) {
                    ProofStatus ps = ((ProofWrapper) value).proof.mgt().getStatus();
                    if (ps.getProofClosed()) {
                        label.setIcon(KEY_CLOSED);
                    } else if (ps.getProofClosedButLemmasLeft()) {
                        label.setIcon(KEY_ALMOST_CLOSED);
                    } else if (ps.getProofClosedByCache()) {
                        label.setIcon(KEY_CACHED_CLOSED);
                    } else {
                        if (!ps.getProofOpen()) {
                            LOGGER.warn("Unknown proof status " + ps
                                + " in ProofManagementDialog. Displaying open icon.");
                        }
                        label.setIcon(KEY_OPEN);
                    }
                }
                return result;
            }
        });
        list.addListSelectionListener(e -> updateContractPanel());

        // create method list panel, scroll pane
        JPanel listPanelByMethod = new JPanel();
        listPanelByMethod.setLayout(new BoxLayout(listPanelByMethod, BoxLayout.X_AXIS));
        JScrollPane classScrollPane = new JScrollPane(tree);
        classScrollPane.setBorder(new TitledBorder("Contract Targets"));
        Dimension classScrollPaneDim = new Dimension(250, 400);
        classScrollPane.setPreferredSize(classScrollPaneDim);
        classScrollPane.setMinimumSize(classScrollPaneDim);
        listPanelByMethod.add(classScrollPane);

        // create proof list panel, scroll pane
        JPanel listPanelByProof = new JPanel();
        listPanelByProof.setLayout(new BoxLayout(listPanelByProof, BoxLayout.X_AXIS));
        JScrollPane proofScrollPane = new JScrollPane(list);
        proofScrollPane.setBorder(new TitledBorder("Proofs"));
        proofScrollPane.setPreferredSize(classScrollPaneDim);
        proofScrollPane.setMinimumSize(classScrollPaneDim);
        listPanelByProof.add(proofScrollPane);

        // create contract panel by method
        contractPanelByMethod = new ContractSelectionPanel(initConfig.getServices(), false);
        contractPanelByMethod.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                if (e.getClickCount() == 2) {
                    startButton.doClick();
                }
            }
        });
        contractPanelByMethod.addListSelectionListener(e -> updateStartButton());
        listPanelByMethod.add(contractPanelByMethod);

        // create contract panel by proof
        contractPanelByProof = new ContractSelectionPanel(initConfig.getServices(), false);
        contractPanelByProof.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                updateStartButton();
                if (e.getClickCount() == 2) {
                    startButton.doClick();
                }
            }
        });
        contractPanelByProof.addListSelectionListener(e -> updateStartButton());
        listPanelByProof.add(contractPanelByProof);

        // create tabbed pane
        JTabbedPane tabPane = new JTabbedPane();
        tabbedPane = tabPane;
        tabPane.addTab("By Target", listPanelByMethod);
        tabPane.addTab("By Proof", listPanelByProof);
        tabPane.addChangeListener(e -> {
            updateStartButton();
            if (list.getSelectedIndex() == -1 && list.getModel().getSize() > 0) {
                list.setSelectedIndex(0);
            }
        });
        getContentPane().add(tabPane);

        // create button panel
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        Dimension buttonDim = new Dimension(140, 27);
        buttonPanel
                .setMaximumSize(new Dimension(Integer.MAX_VALUE, (int) buttonDim.getHeight() + 10));
        getContentPane().add(buttonPanel);

        // create "start proof" button
        startButton = new JButton("Start Proof");
        startButton.setPreferredSize(buttonDim);
        startButton.setMinimumSize(buttonDim);
        startButton.setEnabled(false);
        startButton.addActionListener(e -> {
            Contract contract = getSelectedContract();
            if (contract != null) {
                setVisible(false);
                findOrStartProof(contract);
            }
        });
        buttonPanel.add(startButton);
        getRootPane().setDefaultButton(startButton);

        // create "cancel" button
        cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(buttonDim);
        cancelButton.setMinimumSize(buttonDim);
        cancelButton.addActionListener(e -> setVisible(false));
        buttonPanel.add(cancelButton);
        GuiUtilities.attachClickOnEscListener(cancelButton);

        // show
        getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
        pack();
    }

    @Override
    public void dispose() {
        super.dispose();
        // ============================================
        // cumbersome but necessary code providing a workaround for a memory leak
        // in Java, see: http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=6497929
        tabbedPane = null;
        proofList = null;
        targetIcons = null;
        classTree = null;
        contractPanelByMethod = null;
        contractPanelByProof = null;
        startButton = null;
        cancelButton = null;
        // ============================================
    }

    /**
     * Selects the first contract of the first {@link TypeDeclaration} (sorted by name).
     */
    private void selectKJTandTarget() {
        Services servicesLocal = initConfig.getServices();
        List<KeYJavaType> allJavaTypes = servicesLocal.getJavaInfo().getAllKeYJavaTypes().stream()
                // sort by name
                .sorted(Comparator.comparing(KeYJavaType::getFullName))
                // filter out library classes
                .filter(kjtTmp -> {
                    Object type = kjtTmp.getJavaType();
                    return !(type instanceof TypeDeclaration td && td.isLibraryClass());
                })
                .toList();

        // compare: IProgramMethods by program name, otherwise prefer NOT IProgramMethod
        final Comparator<IObserverFunction> compareFunction = (o1, o2) -> {
            if (o1 instanceof IProgramMethod && !(o2 instanceof IProgramMethod)) {
                return -1;
            } else if (!(o1 instanceof IProgramMethod) && o2 instanceof IProgramMethod) {
                return 1;
            } else {
                String s1 = o1.name() instanceof ProgramElementName
                        ? ((ProgramElementName) o1.name()).getProgramName()
                        : o1.name().toString();
                String s2 = o2.name() instanceof ProgramElementName
                        ? ((ProgramElementName) o2.name()).getProgramName()
                        : o2.name().toString();
                return s1.compareTo(s2);
            }
        };

        for (KeYJavaType javaType : allJavaTypes) {
            Stream<IObserverFunction> targets = servicesLocal.getSpecificationRepository()
                    .getContractTargets(javaType).stream().sorted(compareFunction)
                    // has contract
                    .filter(targetTmp -> !servicesLocal.getSpecificationRepository()
                            .getContracts(javaType, targetTmp).isEmpty());
            Optional<IObserverFunction> t = targets.findFirst();
            if (t.isPresent()) {
                select(javaType, t.get());
                break;
            }
        }
    }

    /**
     * Shows the dialog and selects the passed proof.
     */
    public static void showInstance(InitConfig initConfig, @Nullable Proof selectedProof) {
        showInstance(initConfig, null, null, selectedProof);
    }

    /**
     * <p>
     * Shows the dialog and selects the passed {@link KeYJavaType} and its
     * {@link IObserverFunction}.
     * </p>
     * <p>
     * <b>This method is required, because the Eclipse integration of KeY needs this functionality
     * to start a new proof for a selected method.</b>
     * </p>
     *
     * @param initConfig the initial prover configuration
     * @param selectedKJT the selected {@link KeYJavaType}
     * @param selectedTarget the selected target
     */
    public static void showInstance(InitConfig initConfig, @Nullable KeYJavaType selectedKJT,
            @Nullable IObserverFunction selectedTarget) {
        showInstance(initConfig, selectedKJT, selectedTarget, null);
    }

    /**
     * Shows the dialog.
     */
    public static boolean showInstance(InitConfig initConfig) {
        return showInstance(initConfig, null, null, null);
    }

    private static boolean showInstance(InitConfig initConfig, @Nullable KeYJavaType selectedKJT,
            @Nullable IObserverFunction selectedTarget, @Nullable Proof selectedProof) {
        MainWindow mainWindow = MainWindow.getInstance();
        ProofManagementDialog dialog = new ProofManagementDialog(mainWindow, initConfig);

        // determine own defaults if not given
        dialog.selectKJTandTarget();
        // if (previouslySelectedContracts.containsKey(selectedProof)) {
        if (previouslySelectedContracts != null) {
            dialog.select(previouslySelectedContracts);
        }

        dialog.updateGlobalStatus();

        // The selected elements have to be select before the dialog is made visible!
        if (selectedKJT != null && selectedTarget != null) {
            dialog.select(selectedKJT, selectedTarget);
        }

        if (selectedProof != null) {
            dialog.select(selectedProof);
            dialog.env = selectedProof.getEnv();
        }

        dialog.setLocationRelativeTo(mainWindow);
        dialog.setVisible(true);

        Contract selectedContract = dialog.getSelectedContract();
        if (selectedContract != null) {
            String kjtName = selectedContract.getKJT().getFullName();
            String contractName = selectedContract.getName();
            String methodName = selectedContract.getTarget().name().toString();
            previouslySelectedContracts = new ContractId(kjtName, methodName, contractName);
        }
        return dialog.startedProof;
    }

    /**
     * Selects the contract by the given {@link ContractId}
     */
    private void select(@NonNull ContractId cid) {
        Services servicesLocal = initConfig.getServices();
        String keyJavaTypeName = cid.keyJavaTypeName;
        Optional<KeYJavaType> allJavaTypes =
            servicesLocal.getJavaInfo().getAllKeYJavaTypes().stream()
                    // filter out library classes
                    .filter(kjtTmp -> {
                        Object type = kjtTmp.getJavaType();
                        return !(type instanceof TypeDeclaration td && td.isLibraryClass());
                    })
                    .filter(it -> it.getFullName().equals(keyJavaTypeName)).findAny();

        if (!allJavaTypes.isPresent()) {
            return;
        }
        KeYJavaType javaType = allJavaTypes.get();
        String methodNameString = cid.methodName;
        if (methodNameString == null) {
            return;
        }
        Name methodName = new Name(methodNameString);
        Optional<IObserverFunction> target =
            servicesLocal.getSpecificationRepository().getContractTargets(javaType).stream()
                    .filter(targetTmp -> !servicesLocal.getSpecificationRepository()
                            .getContracts(javaType, targetTmp).isEmpty())
                    .filter(it -> it.name().equals(methodName)).findAny();
        if (!target.isPresent()) {
            return;
        }
        final IObserverFunction method = target.get();
        select(javaType, method);

        if (!isInstanceMethodOfAbstractClass(javaType, method)) {
            Optional<Contract> contract =
                initConfig.getServices().getSpecificationRepository().getContracts(javaType, method)
                        .stream().filter(it -> it.getName().equals(cid.contractName)).findAny();
            ContractSelectionPanel panel = contractPanelByMethod;
            if (panel != null) {
                contract.ifPresent(value -> panel.selectContract(value));
            }
        }
    }

    private @Nullable ContractSelectionPanel getActiveContractPanel() {
        JTabbedPane pane = tabbedPane;
        if (pane == null) {
            return null;
        }
        return pane.getSelectedIndex() == 0 ? contractPanelByMethod : contractPanelByProof;
    }

    private void select(KeYJavaType kjt, IObserverFunction target) {
        JTabbedPane pane = tabbedPane;
        if (pane != null) {
            pane.setSelectedIndex(0);
        }
        if (classTree != null) {
            classTree.select(kjt, target);
        }
    }

    private void select(Proof p) {
        JList<ProofWrapper> list = proofList;
        JTabbedPane pane = tabbedPane;
        if (list == null || pane == null) {
            // the dialog is disposed or not fully built; nothing to select
            return;
        }
        for (int i = 0, n = list.getModel().getSize(); i < n; i++) {
            if (list.getModel().getElementAt(i).proof.equals(p)) {
                pane.setSelectedIndex(1);
                list.setSelectedIndex(i);
                break;
            }
        }
    }

    private @Nullable Contract getSelectedContract() {
        ContractSelectionPanel pan = getActiveContractPanel();
        return pan == null ? null : pan.getContract();
    }

    /**
     * Finds a proof for the given contract. Preferring a already closed proof, laking that a proof
     * that just misses lemmas.
     *
     * @param contract the contract for which to find a proof
     * @return a proof for the contract, preferring closed proofs then closed proofs needing some
     *         lemmas and then just any proof or {@code null} if there is no proof for the contract
     */
    private @Nullable Proof findPreferablyClosedProof(@NonNull Contract contract) {
        // will the contracts here always be atomic?
        // it seems that way, but not completely sure
        ImmutableSet<Proof> proofs =
            initConfig.getServices().getSpecificationRepository().getProofs(contract);
        // no proofs?
        if (proofs.isEmpty()) {
            return null;
        }
        // try to find closed proof
        Proof fallback = null;
        for (Proof proof : proofs) {
            var pcm = proof.mgt();
            if (pcm == null) {
                // a proof without correctness management cannot be evaluated; skip it (the
                // previous code crashed with an NPE here)
                continue;
            }
            final ProofStatus status = pcm.getStatus();
            if (status.getProofClosed()) {
                return proof;
            } else if (fallback == null || status.getProofClosedButLemmasLeft()) {
                fallback = proof;
            }
        }
        return fallback;
    }

    private void findOrStartProof(@NonNull Contract contract) {
        Proof proof = findPreferablyClosedProof(contract);
        if (proof == null) {
            AbstractMediatorUserInterfaceControl ui = mediator.getUI();

            ProblemInitializer pi = new ProblemInitializer(ui, initConfig.getServices(), ui);

            var fileRepo = initConfig.getFileRepo();
            if (fileRepo == null) {
                // interactive proof management always works on a loaded problem which carries a
                // file repository; a missing one is an inconsistent state in which the previous
                // code crashed with an NPE
                throw new NullPointerException("InitConfig has no file repository.");
            }
            // enables to access the FileRepo created in AbstractProblemLoader
            pi.setFileRepo(fileRepo);

            try {
                final ProofOblInput po =
                    contract.createProofObl(initConfig.copyWithServices(initConfig.getServices()));
                final ProofAggregate pl = pi.startProver(initConfig, po);

                if (env == null) {
                    env = ui.createProofEnvironmentAndRegisterProof(po, pl, initConfig);
                } else {
                    env.registerProof(po, pl);
                }
                mediator.getSelectionModel().setSelectedProof(pl.getFirstProof());
            } catch (ProofInputException exc) {
                LOGGER.error("", exc);
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), exc);
            }
        } else {
            mediator.getSelectionModel().setSelectedProof(proof);
        }
        startedProof = true;
        // starting another proof will not execute the ProblemLoader again,
        // so we have to activate the UI here
        if (initConfig.getServices().getSpecificationRepository().getAllProofs().size() > 1) {
            mediator.startInterface(true);
        }
    }

    /**
     * Removes the icon from the given button. {@code JButton.setIcon(null)} is runtime-legal and
     * clears the icon, but the annotated JDK shipped with the nullness checker declares the
     * parameter non-null, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    private static void clearIcon(JButton button) {
        button.setIcon(null);
    }

    private void updateStartButton() {
        JButton button = startButton;
        if (button == null) {
            // the dialog is disposed; nothing to update
            return;
        }
        final Contract contract = getSelectedContract();
        if (contract == null) {
            button.setText("No Contract");
            clearIcon(button);
            button.setEnabled(false);
        } else {
            final Proof proof = findPreferablyClosedProof(contract);
            if (proof == null) {
                button.setText("Start Proof");
                clearIcon(button);
            } else {
                var pcm = proof.mgt();
                if (pcm == null) {
                    // a proof without correctness management cannot be evaluated; fall back to
                    // the plain start action (the previous code crashed with an NPE here)
                    button.setText("Start Proof");
                    clearIcon(button);
                } else {
                    final ProofStatus status = pcm.getStatus();
                    button.setText("Go to Proof");
                    if (status.getProofOpen()) {
                        button.setIcon(KEY_OPEN);
                    } else if (status.getProofClosedButLemmasLeft()) {
                        button.setIcon(KEY_ALMOST_CLOSED);
                    } else if (status.getProofClosedByCache()) {
                        button.setIcon(KEY_CACHED_CLOSED);
                    } else {
                        assert status.getProofClosed();
                        button.setIcon(KEY_CLOSED);
                    }
                }
            }
            button.setEnabled(true);
        }
        validate();
    }

    private boolean isInstanceMethodOfAbstractClass(KeYJavaType p_class, IObserverFunction obs) {
        if (p_class.getJavaType() instanceof InterfaceDeclaration) {
            return true;
        }
        var sort = p_class.getSort();
        return sort != null && sort.isAbstract() && !obs.isStatic();
    }

    private void updateContractPanel() {
        ContractSelectionPanel pan = getActiveContractPanel();
        if (pan == null) {
            // the dialog is disposed or not fully built; nothing to update
            return;
        }
        if (pan == contractPanelByMethod) {
            ClassTree tree = classTree;
            if (tree == null) {
                return;
            }
            final ClassTree.Entry entry = tree.getSelectedEntry();
            final KeYJavaType entryKjt = entry != null ? entry.kjt : null;
            final IObserverFunction entryTarget = entry != null ? entry.target : null;
            if (entryKjt != null && entryTarget != null
                    && !isInstanceMethodOfAbstractClass(entryKjt, entryTarget)) {
                final ImmutableSet<Contract> contracts = initConfig.getServices()
                        .getSpecificationRepository().getContracts(entryKjt, entryTarget);
                pan.setContracts(contracts, "Contracts");

                Map<Pair<KeYJavaType, IObserverFunction>, @Nullable Icon> icons = targetIcons;
                pan.setGrayOutAuxiliaryContracts(icons != null && Objects.equals(
                    icons.get(new Pair<>(entryKjt, entryTarget)), KEY_CLOSED));
            } else {
                pan.setContracts(DefaultImmutableSet.nil(), "Contracts");
            }
        } else if (pan == contractPanelByProof) {
            JList<ProofWrapper> list = proofList;
            if (list != null) {
                ProofWrapper selected = list.getSelectedValue();
                if (selected != null) {
                    final Proof p = selected.proof;
                    var pcm = p.mgt();
                    if (pcm != null) {
                        final ImmutableSet<Contract> usedContracts = pcm.getUsedContracts();
                        pan.setContracts(usedContracts,
                            "Contracts used in proof \"" + p.name() + "\"");
                    } else {
                        pan.setContracts(DefaultImmutableSet.nil(), "Contracts");
                    }
                } else {
                    pan.setContracts(DefaultImmutableSet.nil(), "Contracts");
                }
            }
        }
        updateStartButton();
    }

    private void updateGlobalStatus() {
        // target icons

        Services services = initConfig.getServices();
        SpecificationRepository specRepos = services.getSpecificationRepository();

        var kjts = services.getJavaInfo().getAllKeYJavaTypes();
        for (KeYJavaType kjt : kjts) {
            // skip library classes, the user isn't shown contracts for them
            Object javaType = kjt.getJavaType();
            if (javaType instanceof TypeDeclaration td && td.isLibraryClass()) {
                continue;
            }
            ImmutableSet<IObserverFunction> targets = specRepos.getContractTargets(kjt);
            for (IObserverFunction target : targets) {
                if (!isInstanceMethodOfAbstractClass(kjt, target)) {
                    ImmutableSet<Contract> contracts = specRepos.getContracts(kjt, target);
                    boolean startedProving = false;
                    boolean allClosed = true;
                    boolean lemmasLeft = false;
                    boolean cached = false;
                    for (Contract contract : contracts) {
                        // Skip auxiliary contracts (like block/loop contracts).
                        if (contract.isAuxiliary()) {
                            continue;
                        }
                        final Proof proof = findPreferablyClosedProof(contract);
                        if (proof == null) {
                            allClosed = false;
                        } else {
                            startedProving = true;
                            var pcm = proof.mgt();
                            if (pcm == null) {
                                // a proof without correctness management cannot be evaluated;
                                // treat it as open (the previous code crashed with an NPE here)
                                allClosed = false;
                            } else {
                                ProofStatus status = pcm.getStatus();
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
                    }
                    Map<Pair<KeYJavaType, IObserverFunction>, @Nullable Icon> icons = targetIcons;
                    if (icons != null) {
                        Icon icon = startedProving
                                ? (allClosed
                                        ? (cached ? KEY_CACHED_CLOSED
                                                : lemmasLeft ? KEY_ALMOST_CLOSED : KEY_CLOSED)
                                        : KEY_OPEN)
                                : null;
                        icons.put(new Pair<KeYJavaType, IObserverFunction>(kjt, target), icon);
                    }
                }
            }
        }
        ClassTree tree = classTree;
        if (tree != null) {
            tree.updateUI();
        }

        // proof list
        DefaultListModel<ProofWrapper> model = new DefaultListModel<>();
        for (Proof p : specRepos.getAllProofs()) {
            model.add(0, new ProofWrapper(p));
        }
        JList<ProofWrapper> list = proofList;
        if (list != null) {
            boolean changed;
            if (model.size() != list.getModel().getSize()) {
                changed = true;
            } else {
                changed = false;
                for (int i = 0, n = model.size(); i < n; i++) {
                    if (!model.get(i).equals(list.getModel().getElementAt(i))) {
                        changed = true;
                        break;
                    }
                }
            }
            if (changed) {
                list.setModel(model);
                list.updateUI();
            }
        }

        // others
        updateContractPanel();
        updateStartButton();
    }

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------
    private record ProofWrapper(Proof proof) {
        @Override
        public String toString() {
            return proof.name().toString();
        }

        @Override
        public boolean equals(@Nullable Object o) {
            return o instanceof ProofWrapper(Proof proof1) && proof.equals(proof1);
        }

        @Override
        public int hashCode() {
            return 3 * proof.hashCode();
        }

    }

    /**
     * Stores the identification of a {@link Contract}, i.e. type, method, contract name.
     *
     * @param keyJavaTypeName The key java type name.
     * @param methodName The method name.
     * @param contractName The contract name.
     */
    private record ContractId(
            @Nullable String keyJavaTypeName, @Nullable String methodName,
            @Nullable String contractName) {
    }
}
