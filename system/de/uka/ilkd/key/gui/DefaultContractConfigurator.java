package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.mgt.ContractSet;
import de.uka.ilkd.key.proof.mgt.OldOperationContract;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.ContractConfigurator;
import de.uka.ilkd.key.speclang.IteratorOfClassInvariant;
import de.uka.ilkd.key.speclang.ListOfClassInvariant;
import de.uka.ilkd.key.speclang.SLListOfClassInvariant;

public class DefaultContractConfigurator extends JDialog 
                                         implements ContractConfigurator {

    private SpecificationRepository repos;
    private OldOperationContract base;
    private Modality modality;
    private ListOfClassInvariant preInvs = SLListOfClassInvariant.EMPTY_LIST;
    private ListOfClassInvariant postInvs = SLListOfClassInvariant.EMPTY_LIST;
    private ListOfProgramMethod programMethods;
    private boolean successful;
    private JEditorPane contractTextArea;
    private boolean allowConfig;
    
    public DefaultContractConfigurator(String title, JFrame parent) {
        super(parent, title, true);
    }
    
    public void setSpecification(SpecificationRepository repos) {        
        this.repos = repos;
    }
    
    public void setProgramMethods(ListOfProgramMethod pm) {
        this.programMethods = pm;
    }
    
    public void setModality(Modality modality) {
        this.modality = modality;
    }
    
    public void start() {
        getContentPane().removeAll();
        ContractSet ctSet = repos.getContracts(programMethods, modality);
        ModelMethod mm = ((OldOperationContract)ctSet.iterator().next()).getModelMethod();
        ModelClass mc = mm.getContainingClass();
        final ClassInvariantSelectionPanel selectionPanelPre 
        = new ClassInvariantSelectionPanel(
                mc.getAllClasses(), 
                false,  
                mc, false);
        final ClassInvariantSelectionPanel selectionPanelPost 
        = new ClassInvariantSelectionPanel(
                mc.getAllClasses(), 
                false,  
                mc, false);
        ContractSelectionPanel contractSelectionPanel 
             = new ContractSelectionPanel(ctSet, false);
        
        contractSelectionPanel.addListSelectionListener
            (new ContractListSelectionListener(this));
        
        JComponent tabs;
        if (allowConfig) {
            tabs = new JTabbedPane();
            ((JTabbedPane)tabs).addTab("Base Contract", new JScrollPane(contractSelectionPanel));
            ((JTabbedPane)tabs).addTab("Assumed Invariants", selectionPanelPre);
            ((JTabbedPane)tabs).addTab("Ensured Invariants", selectionPanelPost);     
        } else {
            tabs =new JScrollPane(contractSelectionPanel);
        }
        tabs.setPreferredSize(new Dimension(800, 500));
        getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
                
        contractTextArea = new JEditorPane("text/html","Contract");
        contractTextArea.setEditable(false);
        final Font contractTextAreaFont =  contractTextArea.getFont().deriveFont(Font.PLAIN, 10);
        contractTextArea.setFont(contractTextAreaFont);
        JScrollPane scrollPane = new JScrollPane(contractTextArea);
        scrollPane.setPreferredSize(new Dimension(200, 150));
        scrollPane.setBorder(new TitledBorder("Configured Contract"));
        
        JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT, tabs, scrollPane);
        splitPane.setResizeWeight(.75);
        splitPane.setDividerLocation(.75);
        splitPane.resetToPreferredSizes();
        getContentPane().add(splitPane);
        
        JPanel buttons = new JPanel();
        buttons.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        buttons.setPreferredSize(new Dimension(400, 40));

        Dimension buttonDim = new Dimension(95, 25);

        //      create "ok" button
        JButton okButton = new JButton("OK");
        okButton.setPreferredSize(buttonDim);
        okButton.setMinimumSize(buttonDim);
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                successful = true;
                setVisible(false);
            }
        });
        buttons.add(okButton);
        getRootPane().setDefaultButton(okButton);

        //create "cancel" button
        JButton cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(buttonDim);
        cancelButton.setMinimumSize(buttonDim);
        cancelButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
            }
        });
        buttons.add(cancelButton);

        getContentPane().add(buttons);
        
        selectionPanelPre.addInvariantSelectionListener(new ListSelectionListener() {
            public void valueChanged(ListSelectionEvent e) {
                setPreInvs(selectionPanelPre.getClassInvariants());
            }
        });
        
        selectionPanelPost.addInvariantSelectionListener(new ListSelectionListener() {
            public void valueChanged(ListSelectionEvent e) {
                setPostInvs(selectionPanelPost.getClassInvariants());                
            }
        });
        
        updateContractWithBase((OldOperationContract)contractSelectionPanel.getCurrentSelection());
        setPostInvs(selectionPanelPost.getClassInvariants());
        setPreInvs(selectionPanelPre.getClassInvariants());
        
        pack();
        setVisible(true);
    }
    
    public OldOperationContract getMethodContract() {        
        return base;
    }
    
    public ListOfClassInvariant getPreInvariants() {
        return preInvs;
    }
    
    public ListOfClassInvariant getPostInvariants() {
        return postInvs;
    }
    
    public boolean wasSuccessful() {
        return successful;
    }
    
    public void updateDisplay() {
        StringBuffer sb = new StringBuffer();
        sb.append("<html><p style=\"font-family: lucida;font-size: 11pt\"><b>pre:</b> "+ base.getPreText());
        IteratorOfClassInvariant it = preInvs.iterator();
        while (it.hasNext()) {
            sb.append("<br><b>pre:</b> ");
            sb.append(it.next().toString());
        }
        sb.append("<br><b>modifies:</b> "+base.getModifiesText());
        sb.append("<br><b>post:</b> "+ base.getPostText());
        it = postInvs.iterator();
        while (it.hasNext()) {
            sb.append("<br><b>post:</b> ");
            sb.append(it.next().toString());
        }        
        sb.append("</p></html>");
        contractTextArea.setText(sb.toString());        
        repaint();
    }
    
    public void updateContractWithBase(OldOperationContract mc) {
        base = mc;
        updateDisplay();
    }
    
    public void setPreInvs(ListOfClassInvariant preInvs) {
        this.preInvs = preInvs;
        updateDisplay();
    }
    
    public void setPostInvs(ListOfClassInvariant postInvs) {
        this.postInvs = postInvs;
        updateDisplay();
    }
    
    public void clear() {
        //do nothing, we create an instance of this class each time
    }
    
    public void allowConfiguration(boolean allowConfig) {
        this.allowConfig = allowConfig;
    }
    
    class ContractListSelectionListener implements ListSelectionListener {
        
        private DefaultContractConfigurator conf;
                
        ContractListSelectionListener(DefaultContractConfigurator conf) {
            this.conf = conf;
        }
        
        public void valueChanged(ListSelectionEvent e) {
            conf.updateContractWithBase((OldOperationContract) 
                    ((JList)e.getSource()).getSelectedValue());
        }
    
        
    }
    
}
