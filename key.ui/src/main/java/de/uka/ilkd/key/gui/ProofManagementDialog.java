/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.Name;
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
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public final class ProofManagementDialog extends JDialog {

    private static final long serialVersionUID = 3543411893273433386L;
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofManagementDialog.class);

    /**
     * The contracts are stored by name of the {@link KeYJavaType}, method name, and contract name
     * to avoid keeping environments in the memory.
     */
    @Nullable
    private static ContractId previouslySelectedContracts;

    private static final ImageIcon KEY_OPEN = IconFactory.keyHole(20, 20);
    private static final ImageIcon KEY_ALMOST_CLOSED = IconFactory.keyHoleAlmostClosed(20, 20);
    private static final ImageIcon KEY_CACHED_CLOSED = IconFactory.keyCachedClosed(20, 20);
    private static final Icon KEY_CLOSED = IconFactory.keyHoleClosed(20);
    private boolean startedProof;
    private JTabbedPane tabbedPane;
    private Map<Pair<KeYJavaType, IObserverFunction>, Icon> targetIcons;
    private ClassTree classTree;
    private JList<ProofWrapper> proofList;
    private ContractSelectionPanel contractPanelByMethod;
    private ContractSelectionPanel contractPanelByProof;
    private JButton startButton;
    private JButton cancelButton;
    private final KeYMediator mediator;
    private final InitConfig initConfig;
    private ProofEnvironment env;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------
    private ProofManagementDialog(MainWindow mainWindow, final InitConfig initConfig) {
        super(mainWindow, "Proof Management", true);
        this.mediator = mainWindow.getMediator();
        this.initConfig = initConfig;

        // create class tree
        targetIcons = new LinkedHashMap<>();
        classTree = new ClassTree(true, true, initConfig.getServices(), targetIcons);
        classTree.addMouseListener(new MouseAdapter() {
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
        classTree.addTreeSelectionListener(e -> updateContractPanel());

        // create proof list
        proofList = new JList<>();
        proofList.setCellRenderer(new DefaultListCellRenderer() {
            private static final long serialVersionUID = -7810888250050777877L;

            @Override
            public Component getListCellRendererComponent(JList<?> list, Object value, int index,
                    boolean isSelected, boolean cellHasFocus) {
                Component result = super.getListCellRendererComponent(list, value, index,
                    isSelected, cellHasFocus);

                if (result instanceof JLabel) {
                    ProofStatus ps = ((ProofWrapper) value).proof.mgt().getStatus();
                    JLabel label = (JLabel) result;
                    if (ps.getProofClosed()) {
                        label.setIcon(KEY_CLOSED);
                    } else if (ps.getProofClosedButLemmasLeft()) {
                        label.setIcon(KEY_ALMOST_CLOSED);
                    } else if (ps.getProofClosedByCache()) {
                        label.setIcon(KEY_CACHED_CLOSED);
                    } else {
                        assert ps.getProofOpen();
                        label.setIcon(KEY_OPEN);
                    }
                }
                return result;
            }
        });
        proofList.addListSelectionListener(e -> updateContractPanel());

        // create method list panel, scroll pane
        JPanel listPanelByMethod = new JPanel();
        listPanelByMethod.setLayout(new BoxLayout(listPanelByMethod, BoxLayout.X_AXIS));
        JScrollPane classScrollPane = new JScrollPane(classTree);
        classScrollPane.setBorder(new TitledBorder("Contract Targets"));
        Dimension classScrollPaneDim = new Dimension(250, 400);
        classScrollPane.setPreferredSize(classScrollPaneDim);
        classScrollPane.setMinimumSize(classScrollPaneDim);
        listPanelByMethod.add(classScrollPane);

        // create proof list panel, scroll pane
        JPanel listPanelByProof = new JPanel();
        listPanelByProof.setLayout(new BoxLayout(listPanelByProof, BoxLayout.X_AXIS));
        JScrollPane proofScrollPane = new JScrollPane(proofList);
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
        tabbedPane = new JTabbedPane();
        tabbedPane.addTab("By Target", listPanelByMethod);
        tabbedPane.addTab("By Proof", listPanelByProof);
        tabbedPane.addChangeListener(e -> {
            updateStartButton();
            if (proofList.getSelectedIndex() == -1 && proofList.getModel().getSize() > 0) {
                proofList.setSelectedIndex(0);
            }
        });
        getContentPane().add(tabbedPane);

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
                .filter(kjtTmp -> !(kjtTmp.getJavaType() instanceof TypeDeclaration
                        && ((TypeDeclaration) kjtTmp.getJavaType()).isLibraryClass()))
                .collect(Collectors.toList());

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
    public static void showInstance(InitConfig initConfig, Proof selectedProof) {
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
    public static void showInstance(InitConfig initConfig, KeYJavaType selectedKJT,
            IObserverFunction selectedTarget) {
        showInstance(initConfig, selectedKJT, selectedTarget, null);
    }

    /**
     * Shows the dialog.
     */
    public static boolean showInstance(InitConfig initConfig) {
        return showInstance(initConfig, null, null, null);
    }

    private static boolean showInstance(InitConfig initConfig, KeYJavaType selectedKJT,
            IObserverFunction selectedTarget, Proof selectedProof) {
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

        if (dialog.getSelectedContract() != null) {
            Contract c = dialog.getSelectedContract();
            String kjtName = c.getKJT().getFullName();
            String contractName = c.getName();
            String methodName = c.getTarget().name().toString();
            previouslySelectedContracts = new ContractId(kjtName, methodName, contractName);
        }
        return dialog.startedProof;
    }

    /**
     * Selects the contract by the given {@link ContractId}
     */
    private void select(@Nonnull ContractId cid) {
        Services servicesLocal = initConfig.getServices();
        String keyJavaTypeName = cid.keyJavaTypeName;
        Optional<KeYJavaType> allJavaTypes =
            servicesLocal.getJavaInfo().getAllKeYJavaTypes().stream()
                    // filter out library classes
                    .filter(kjtTmp -> !(kjtTmp.getJavaType() instanceof TypeDeclaration
                            && ((TypeDeclaration) kjtTmp.getJavaType()).isLibraryClass()))
                    .filter(it -> it.getFullName().equals(keyJavaTypeName)).findAny();

        if (!allJavaTypes.isPresent()) {
            return;
        }
        KeYJavaType javaType = allJavaTypes.get();
        Name methodName = new Name(cid.methodName);
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
            contract.ifPresent(value -> contractPanelByMethod.selectContract(value));
        }
    }

    private ContractSelectionPanel getActiveContractPanel() {
        return tabbedPane.getSelectedIndex() == 0 ? contractPanelByMethod : contractPanelByProof;
    }

    private void select(KeYJavaType kjt, IObserverFunction target) {
        tabbedPane.setSelectedIndex(0);
        if (classTree != null) {
            classTree.select(kjt, target);
        }
    }

    private void select(Proof p) {
        for (int i = 0, n = proofList.getModel().getSize(); i < n; i++) {
            if (proofList.getModel().getElementAt(i).proof.equals(p)) {
                tabbedPane.setSelectedIndex(1);
                proofList.setSelectedIndex(i);
                break;
            }
        }
    }

    private Contract getSelectedContract() {
        return getActiveContractPanel().getContract();
    }

    /**
     * Finds a proof for the given contract. Preferring a already closed proof, laking that a proof
     * that just misses lemmas.
     *
     * @param contract the contract for which to find a proof
     * @return a proof for the contract, preferring closed proofs then closed proofs needing some
     *         lemmas and then just any proof or {@code null} if there is no proof for the contract
     */
    @Nullable
    private Proof findPreferablyClosedProof(@Nonnull Contract contract) {
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
            final ProofStatus status = proof.mgt().getStatus();
            if (status.getProofClosed()) {
                return proof;
            } else if (fallback == null || status.getProofClosedButLemmasLeft()) {
                fallback = proof;
            }
        }
        return fallback;
    }

    private void findOrStartProof(@Nonnull Contract contract) {
        Proof proof = findPreferablyClosedProof(contract);
        if (proof == null) {
            AbstractMediatorUserInterfaceControl ui = mediator.getUI();

            ProblemInitializer pi = new ProblemInitializer(ui, initConfig.getServices(), ui);

            // enables to access the FileRepo created in AbstractProblemLoader
            pi.setFileRepo(initConfig.getFileRepo());

            try {
                final ProofOblInput po =
                    contract.createProofObl(initConfig.copyWithServices(initConfig.getServices()));
                final ProofAggregate pl = pi.startProver(initConfig, po);

                if (env == null) {
                    env = ui.createProofEnvironmentAndRegisterProof(po, pl, initConfig);
                } else {
                    env.registerProof(po, pl);
                }
            } catch (ProofInputException exc) {
                LOGGER.error("", exc);
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), exc);
            }
        } else {
            mediator.setProof(proof);
        }
        startedProof = true;
        // starting another proof will not execute the ProblemLoader again,
        // so we have to activate the UI here
        if (initConfig.getServices().getSpecificationRepository().getAllProofs().size() > 1) {
            mediator.startInterface(true);
        }
    }

    private void updateStartButton() {
        final Contract contract = getSelectedContract();
        if (contract == null) {
            startButton.setText("No Contract");
            startButton.setIcon(null);
            startButton.setEnabled(false);
        } else {
            final Proof proof = findPreferablyClosedProof(contract);
            if (proof == null) {
                startButton.setText("Start Proof");
                startButton.setIcon(null);
            } else {
                final ProofStatus status = proof.mgt().getStatus();
                startButton.setText("Go to Proof");
                if (status.getProofOpen()) {
                    startButton.setIcon(KEY_OPEN);
                } else if (status.getProofClosedButLemmasLeft()) {
                    startButton.setIcon(KEY_ALMOST_CLOSED);
                } else {
                    assert status.getProofClosed();
                    startButton.setIcon(KEY_CLOSED);
                }
            }
            startButton.setEnabled(true);
        }
        validate();
    }


    private boolean isInstanceMethodOfAbstractClass(KeYJavaType p_class, IObserverFunction obs) {
        return p_class.getJavaType() instanceof InterfaceDeclaration
                || (p_class.getSort().isAbstract() && !obs.isStatic());
    }

    private void updateContractPanel() {
        ContractSelectionPanel pan = getActiveContractPanel();
        if (pan == contractPanelByMethod) {
            final ClassTree.Entry entry = classTree.getSelectedEntry();
            if (entry != null && entry.target != null
                    && !isInstanceMethodOfAbstractClass(entry.kjt, entry.target)) {
                final ImmutableSet<Contract> contracts = initConfig.getServices()
                        .getSpecificationRepository().getContracts(entry.kjt, entry.target);
                pan.setContracts(contracts, "Contracts");

                pan.setGrayOutAuxiliaryContracts(Objects.equals(
                    targetIcons.get(new Pair<>(entry.kjt, entry.target)), KEY_CLOSED));
            } else {
                pan.setContracts(DefaultImmutableSet.nil(), "Contracts");
            }
        } else if (pan == contractPanelByProof) {
            if (proofList.getSelectedValue() != null) {
                final Proof p = proofList.getSelectedValue().proof;
                final ImmutableSet<Contract> usedContracts = p.mgt().getUsedContracts();
                pan.setContracts(usedContracts, "Contracts used in proof \"" + p.name() + "\"");
            } else {
                pan.setContracts(DefaultImmutableSet.nil(), "Contracts");
            }
        }
        updateStartButton();
    }

    private void updateGlobalStatus() {
        // target icons

        Services services = initConfig.getServices();
        SpecificationRepository specRepos = services.getSpecificationRepository();


        Set<KeYJavaType> kjts = services.getJavaInfo().getAllKeYJavaTypes();
        for (KeYJavaType kjt : kjts) {
            // skip library classes, the user isn't shown contracts for them
            if (kjt.getJavaType() instanceof TypeDeclaration
                    && ((TypeDeclaration) kjt.getJavaType()).isLibraryClass()) {
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
                    targetIcons.put(new Pair<>(kjt, target),
                        startedProving
                                ? (allClosed
                                        ? (cached ? KEY_CACHED_CLOSED
                                                : lemmasLeft ? KEY_ALMOST_CLOSED : KEY_CLOSED)
                                        : KEY_OPEN)
                                : null);
                }
            }
        }
        classTree.updateUI();

        // proof list
        DefaultListModel<ProofWrapper> model = new DefaultListModel<>();
        for (Proof p : specRepos.getAllProofs()) {
            model.add(0, new ProofWrapper(p));
        }
        boolean changed;
        if (model.size() != proofList.getModel().getSize()) {
            changed = true;
        } else {
            changed = false;
            for (int i = 0, n = model.size(); i < n; i++) {
                if (!model.get(i).equals(proofList.getModel().getElementAt(i))) {
                    changed = true;
                    break;
                }
            }
        }
        if (changed) {
            proofList.setModel(model);
            proofList.updateUI();
        }

        // others
        updateContractPanel();
        updateStartButton();
    }


    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------
    private static final class ProofWrapper {

        public final Proof proof;

        public ProofWrapper(Proof proof) {
            this.proof = proof;
        }

        @Override
        public String toString() {
            return proof.name().toString();
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof ProofWrapper && proof.equals(((ProofWrapper) o).proof);
        }

        @Override
        public int hashCode() {
            return proof.hashCode();
        }
    }


    /**
     * Stores the identification of a {@link Contract}, i.e. type, method, contract name.
     */
    private static final class ContractId {
        /** The key java type name. */
        @Nullable
        public final String keyJavaTypeName;
        /** The method name. */
        @Nullable
        public final String methodName;
        /** The contract name. */
        @Nullable
        public final String contractName;

        private ContractId(@Nullable String keyJavaTypeName, @Nullable String methodName,
                @Nullable String contractName) {
            this.keyJavaTypeName = keyJavaTypeName;
            this.methodName = methodName;
            this.contractName = contractName;
        }
    }
}
