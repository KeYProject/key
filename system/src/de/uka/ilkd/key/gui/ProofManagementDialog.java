// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
// 
package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import javax.swing.BoxLayout;
import javax.swing.DefaultListCellRenderer;
import javax.swing.DefaultListModel;
import javax.swing.Icon;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.KeyStroke;
import javax.swing.border.TitledBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofStatus;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.key.util.Pair;

public final class ProofManagementDialog extends JDialog {

    private static final ImageIcon keyIcon = IconFactory.keyHole(20, 20);
    private static final ImageIcon keyAlmostClosedIcon = IconFactory.keyHoleAlmostClosed(20, 20);
    private static final ImageIcon keyClosedIcon = IconFactory.keyHoleClosed(20, 20);
    private static boolean startedProof;
    private InitConfig initConfig;
    private Services services;
    private SpecificationRepository specRepos;
    private JTabbedPane tabbedPane;
    private Map<Pair<KeYJavaType, IObserverFunction>, Icon> targetIcons;
    private ClassTree classTree;
    private JList proofList;
    private ContractSelectionPanel contractPanelByMethod;
    private ContractSelectionPanel contractPanelByProof;
    private JButton startButton;
    private JButton cancelButton;
    private KeYMediator mediator;
    private final MainWindow mainWindow;

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    private ProofManagementDialog(MainWindow mainWindow, InitConfig initConfig) {
        super(mainWindow, "Proof Management", true);
        this.mainWindow = mainWindow;
        this.initConfig = initConfig;
        this.services = initConfig.getServices();
        this.specRepos = initConfig.getServices().getSpecificationRepository();
        this.mediator = mainWindow.getMediator();

        //create class tree
        targetIcons = new LinkedHashMap<Pair<KeYJavaType, IObserverFunction>, Icon>();
        classTree = new ClassTree(true, true, services, targetIcons);
        classTree.addTreeSelectionListener(new TreeSelectionListener() {
            public void valueChanged(TreeSelectionEvent e) {
                updateContractPanel();
            }
        });

        //create proof list
        proofList = new JList();
        proofList.setCellRenderer(new DefaultListCellRenderer() {
            @Override
            public Component getListCellRendererComponent(JList list,
                    Object value, int index,
                    boolean isSelected, boolean cellHasFocus) {
                Component result = super.getListCellRendererComponent(list,
                        value, index, isSelected, cellHasFocus);

                if (result instanceof JLabel) {
                    ProofStatus ps = ((ProofWrapper) value).proof.mgt().getStatus();
                    JLabel label = (JLabel) result;
                    if (ps.getProofClosed()) {
                        label.setIcon(keyClosedIcon);
                    } else if (ps.getProofClosedButLemmasLeft()) {
                        label.setIcon(keyAlmostClosedIcon);
                    } else {
                        assert ps.getProofOpen();
                        label.setIcon(keyIcon);
                    }
                }
                return result;
            }
        });
        proofList.addListSelectionListener(new ListSelectionListener() {
            public void valueChanged(ListSelectionEvent e) {
                updateContractPanel();
            }
        });

        //create method list panel, scroll pane
        JPanel listPanelByMethod = new JPanel();
        listPanelByMethod.setLayout(new BoxLayout(listPanelByMethod,
                BoxLayout.X_AXIS));
        JScrollPane classScrollPane = new JScrollPane(classTree);
        classScrollPane.setBorder(new TitledBorder("Contract Targets"));
        Dimension classScrollPaneDim = new Dimension(250, 400);
        classScrollPane.setPreferredSize(classScrollPaneDim);
        classScrollPane.setMinimumSize(classScrollPaneDim);
        listPanelByMethod.add(classScrollPane);

        //create proof list panel, scroll pane	
        JPanel listPanelByProof = new JPanel();
        listPanelByProof.setLayout(new BoxLayout(listPanelByProof,
                BoxLayout.X_AXIS));
        JScrollPane proofScrollPane = new JScrollPane(proofList);
        proofScrollPane.setBorder(new TitledBorder("Proofs"));
        proofScrollPane.setPreferredSize(classScrollPaneDim);
        proofScrollPane.setMinimumSize(classScrollPaneDim);
        listPanelByProof.add(proofScrollPane);

        //create contract panel by method
        contractPanelByMethod = new ContractSelectionPanel(services, false);
        contractPanelByMethod.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                if (e.getClickCount() == 2) {
                    startButton.doClick();
                }
            }
        });
        contractPanelByMethod.addListSelectionListener(
                new ListSelectionListener() {
            public void valueChanged(ListSelectionEvent e) {
                updateStartButton();
            }
        });
        listPanelByMethod.add(contractPanelByMethod);

        //create contract panel by proof
        contractPanelByProof = new ContractSelectionPanel(services, false);
        contractPanelByProof.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                updateStartButton();
                if (e.getClickCount() == 2) {
                    startButton.doClick();
                }
            }
        });
        contractPanelByProof.addListSelectionListener(new ListSelectionListener() {
            public void valueChanged(ListSelectionEvent e) {
                updateStartButton();
            }
        });
        listPanelByProof.add(contractPanelByProof);

        //create tabbed pane
        tabbedPane = new JTabbedPane();
        tabbedPane.addTab("By Target", listPanelByMethod);
        tabbedPane.addTab("By Proof", listPanelByProof);
        tabbedPane.addChangeListener(new ChangeListener() {
            public void stateChanged(ChangeEvent e) {
                updateStartButton();
                if (proofList.getSelectedIndex() == -1
                        && proofList.getModel().getSize() > 0) {
                    proofList.setSelectedIndex(0);
                }
            }
        });
        getContentPane().add(tabbedPane);

        //create button panel
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        Dimension buttonDim = new Dimension(140, 27);
        buttonPanel.setMaximumSize(new Dimension(Integer.MAX_VALUE,
                (int) buttonDim.getHeight()
                + 10));
        getContentPane().add(buttonPanel);

        //create "start proof" button
        startButton = new JButton("Start Proof");
        startButton.setPreferredSize(buttonDim);
        startButton.setMinimumSize(buttonDim);
        startButton.setEnabled(false);
        startButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                ProofOblInput po = createPOForSelectedContract();
                if (po != null) {
                    setVisible(false);
                    findOrStartProof(po);
                }
            }
        });
        buttonPanel.add(startButton);
        getRootPane().setDefaultButton(startButton);

        //create "cancel" button
        cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(buttonDim);
        cancelButton.setMinimumSize(buttonDim);
        cancelButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
            }
        });
        buttonPanel.add(cancelButton);
        ActionListener escapeListener = new ActionListener() {
            public void actionPerformed(ActionEvent event) {
                if (event.getActionCommand().equals("ESC")) {
                    cancelButton.doClick();
                }
            }
        };
        cancelButton.registerKeyboardAction(
                escapeListener,
                "ESC",
                KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                JComponent.WHEN_IN_FOCUSED_WINDOW);

        //show
        getContentPane().setLayout(new BoxLayout(getContentPane(),
                BoxLayout.Y_AXIS));
        pack();
        final Point mainLoc = mainWindow.getLocation();
        setLocation(mainLoc.x + 20, mainLoc.y + 20);
    }

    @Override
    public void dispose() {
        super.dispose();
        //============================================
        // cumbersome but necessary code providing a workaround for a memory leak 
        // in Java, see: http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=6497929
        initConfig = null;
        services = null;
        specRepos = null;
        tabbedPane = null;
        proofList = null;
        targetIcons = null;
        classTree = null;
        contractPanelByMethod = null;
        contractPanelByProof = null;
        startButton = null;
        cancelButton = null;
        //============================================
    }

    private void selectKJTandTarget() {

        KeYJavaType selectedKJT = null;
        IObserverFunction selectedTarget = null;

        Services servicesLocal = initConfig.getServices();
        Set<KeYJavaType> kjts = servicesLocal.getJavaInfo().getAllKeYJavaTypes();
        final KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
        Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
            public int compare(KeYJavaType o1, KeYJavaType o2) {
                return o1.getFullName().compareTo(o2.getFullName());
            }
        });
        outer:
        for (KeYJavaType kjtTmp : kjtsarr) {
            if (kjtTmp.getJavaType() instanceof TypeDeclaration
                    && ((TypeDeclaration) kjtTmp.getJavaType())
                    .isLibraryClass()) {
                continue;
            }
            final ImmutableSet<IObserverFunction> targets = servicesLocal.getSpecificationRepository()
                    .getContractTargets(kjtTmp);
            final IObserverFunction[] targetsArr = targets.toArray(new IObserverFunction[targets.size()]);
            Arrays.sort(targetsArr, new Comparator<IObserverFunction>() {
                public int compare(IObserverFunction o1,
                        IObserverFunction o2) {
                    if (o1 instanceof IProgramMethod
                            && !(o2 instanceof IProgramMethod)) {
                        return -1;
                    } else if (!(o1 instanceof IProgramMethod)
                            && o2 instanceof IProgramMethod) {
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
                }
            });
            for (IObserverFunction targetTmp : targetsArr) {
                if (!servicesLocal.getSpecificationRepository()
                        .getContracts(kjtTmp, targetTmp)
                        .isEmpty()) {
                    selectedKJT = kjtTmp;
                    selectedTarget = targetTmp;
                    break outer;
                }
            }
        }

        validateNotNull(selectedKJT);
        validateNotNull(selectedTarget);
        select(selectedKJT, selectedTarget);
    }

    /*
     * Check for Nullpointers.
     */
    public static void validateNotNull(Object o) {
        if (o == null) {
            System.err.println("Unexpected null value.");
            Thread.dumpStack();
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
     * Shows the dialog and selects the passed {@link KeYJavaType} and its {@link IObserverFunction}.
     * </p>
     * <p>
     * <b>This method is required, because the Eclipse integration of KeY
     * needs this functionality to start a new proof for a selected method.</b>
     * </p>
     */
    public static void showInstance(InitConfig initConfig, KeYJavaType selectedKJT, IObserverFunction selectedTarget) {
       showInstance(initConfig, selectedKJT, selectedTarget, null);
    }

    /**
     * Shows the dialog.
     */
    public static void showInstance(InitConfig initConfig) {
       showInstance(initConfig, null, null, null);
    }
    
    private static void showInstance(InitConfig initConfig, KeYJavaType selectedKJT, IObserverFunction selectedTarget, Proof selectedProof) {

       MainWindow mainWindow = MainWindow.getInstance();
       ProofManagementDialog instance = mainWindow.getProofManagementDialog();

       if (instance == null || instance.initConfig != initConfig) {

           // initConfig has changed --> create new instance
           if (instance != null) {
               instance.dispose();
           }
           instance = new ProofManagementDialog(mainWindow, initConfig);
           mainWindow.setProofManagementDialog(instance);

           //determine own defaults if not given
           instance.selectKJTandTarget();
       }

       startedProof = false;
       instance.updateGlobalStatus();
       
       // The selected elements have to be select before the dialog is made visible!
       if (selectedKJT != null && selectedTarget != null) {
          instance.select(selectedKJT, selectedTarget);
       }
       
       if (selectedProof != null) {
          instance.select(selectedProof);
       }
       
       instance.setVisible(true);
   }

    private ContractSelectionPanel getActiveContractPanel() {
        return tabbedPane.getSelectedIndex() == 0
                ? contractPanelByMethod
                : contractPanelByProof;
    }

    private void select(KeYJavaType kjt, IObserverFunction target) {
        tabbedPane.setSelectedIndex(0);
        classTree.select(kjt, target);
    }

    private void select(Proof p) {
        for (int i = 0, n = proofList.getModel().getSize(); i < n; i++) {
            if (((ProofWrapper) proofList.getModel()
                    .getElementAt(i)).proof.equals(p)) {
                tabbedPane.setSelectedIndex(1);
                proofList.setSelectedIndex(i);
                break;
            }
        }
    }

    private ProofOblInput createPOForSelectedContract() {
        final Contract contract = getActiveContractPanel().getContract();
        return contract == null
                ? null
                : contract.createProofObl(initConfig, contract);
    }

    private Proof findPreferablyClosedProof(ProofOblInput po) {
        ImmutableSet<Proof> proofs = specRepos.getProofs(po);

        //no proofs?
        if (proofs.isEmpty()) {
            return null;
        }

        //try to find closed proof
        for (Proof proof : proofs) {
            if (proof.mgt().getStatus().getProofClosed()) {
                return proof;
            }
        }

        //just take any proof
        return proofs.iterator().next();
    }

    private void findOrStartProof(ProofOblInput po) {
        Proof proof = findPreferablyClosedProof(po);
        if (proof == null) {
            UserInterface ui = mediator.getUI();
            ProblemInitializer pi =
                    new ProblemInitializer(ui, services, true, ui);
            try {
                pi.startProver(initConfig, po, 0);
            } catch (ProofInputException exc) {
                ExceptionDialog.showDialog(MainWindow.getInstance(), exc);
            }
        } else {
            mediator.setProof(proof);
        }
        startedProof = true;
    }

    private void updateStartButton() {
        final ProofOblInput po = createPOForSelectedContract();
        if (po == null) {
            startButton.setText("No Contract");
            startButton.setIcon(null);
            startButton.setEnabled(false);
        } else {
            final Proof proof = findPreferablyClosedProof(po);
            if (proof == null) {
                startButton.setText("Start Proof");
                startButton.setIcon(null);
            } else {
                final ProofStatus status = proof.mgt().getStatus();
                if (status.getProofOpen()) {
                    startButton.setText("Go to Proof");
                    startButton.setIcon(keyIcon);
                } else if (status.getProofClosedButLemmasLeft()) {
                    startButton.setText("Go to Proof");
                    startButton.setIcon(keyAlmostClosedIcon);
                } else {
                    assert status.getProofClosed();
                    startButton.setText("Go to Proof");
                    startButton.setIcon(keyClosedIcon);
                }
            }
            startButton.setEnabled(true);
        }
    }

    private void updateContractPanel() {
        if (getActiveContractPanel() == contractPanelByMethod) {
            final ClassTree.Entry entry = classTree.getSelectedEntry();
            if (entry != null && entry.target != null) {
                final ImmutableSet<Contract> contracts = specRepos.getContracts(entry.kjt, entry.target);
                getActiveContractPanel().setContracts(contracts, "Contracts");
            } else {
                getActiveContractPanel().setContracts(
                        DefaultImmutableSet.<Contract>nil(), "Contracts");
            }
        } else {
            if (proofList.getSelectedValue() != null) {
                final Proof p = ((ProofWrapper) proofList.getSelectedValue()).proof;
                final ImmutableSet<Contract> usedContracts = p.mgt().getUsedContracts();
                getActiveContractPanel().setContracts(usedContracts,
                        "Contracts used in proof \""
                        + p.name() + "\"");
            } else {
                getActiveContractPanel().setContracts(
                        DefaultImmutableSet.<Contract>nil(), "Contracts");
            }
        }
        updateStartButton();
    }

    private void updateGlobalStatus() {
        //target icons
        Set<KeYJavaType> kjts = services.getJavaInfo().getAllKeYJavaTypes();
        for (KeYJavaType kjt : kjts) {
            ImmutableSet<IObserverFunction> targets = specRepos.getContractTargets(kjt);
            for (IObserverFunction target : targets) {
                ImmutableSet<Contract> contracts = specRepos.getContracts(kjt, target);
                boolean startedProving = false;
                boolean allClosed = true;
                boolean lemmasLeft = false;
                for (Contract contract : contracts) {
                    final ProofOblInput po = contract.createProofObl(initConfig, contract);
                    Proof proof = findPreferablyClosedProof(po);
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
                    }
                }
                targetIcons.put(new Pair<KeYJavaType, IObserverFunction>(kjt, target),
                        startedProving
                        ? (allClosed
                        ? (lemmasLeft
                        ? keyAlmostClosedIcon
                        : keyClosedIcon)
                        : keyIcon)
                        : null);
            }
        }
        classTree.updateUI();

        //proof list
        DefaultListModel model = new DefaultListModel();
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

        //others
        updateContractPanel();
        updateStartButton();
    }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    /**
     * Tells whether the last call to a showInstance() method lead to starting a
     * proof.
     */
    public static boolean startedProof() {
        return startedProof;
    }

    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------
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
            return o instanceof ProofWrapper
                    && proof.equals(((ProofWrapper) o).proof);
        }

        @Override
        public int hashCode() {
            return proof.hashCode();
        }
    }
}
