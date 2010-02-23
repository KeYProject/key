package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.*;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IWorkingSpaceOp;
import de.uka.ilkd.key.logic.op.WorkingSpaceRigidOp;
import de.uka.ilkd.key.proof.ProofSaver;
import de.uka.ilkd.key.speclang.OperationContract;

public class WorkingSpaceContractDialog extends JDialog {

    LinkedList specs;
    boolean successful;
    OperationContract spec;
    int compare=1;
    Term cond;
    Term wso;
    final Services services;
    
    public WorkingSpaceContractDialog(String title, JFrame parent, 
            Services services, Term wso) {
        super(parent, title, true);
        this.services = services;
        this.wso = wso;
    }
    
    public void setSpecifications(ImmutableSet<OperationContract> specSet){
        this.specs = new LinkedList();
        Iterator it = specSet.iterator();
        while(it.hasNext()){
            specs.add(it.next());
        }
    }
    
    public void setCondition(Term cond){
        this.cond = cond;
    }
    
    public void setWorkingSpaceOpTerm(Term wso){
        assert wso.op() instanceof IWorkingSpaceOp;
        this.wso = wso;
        if(wso.op() instanceof WorkingSpaceRigidOp){
            setCondition(((WorkingSpaceRigidOp) wso.op()).getPre());
        }
    }
    
    public void start() {
        getContentPane().removeAll();
        JPanel listPanel=new JPanel();

        listPanel.setLayout(new BoxLayout(listPanel, BoxLayout.X_AXIS));
        
        final JList specList = new JList(new Vector(specs));
        
        specList.setSelectedIndex(0);
        specList.setCellRenderer(new PreCondRenderer());

        
//        specList.setCellRenderer(new TextAreaRenderer());
        JScrollPane specListScroll = new
            JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, 
                        JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        specListScroll.getViewport().setView(specList);
        specListScroll.setBorder(new TitledBorder("Method Specs"));

        listPanel.add(specListScroll);
        
        JPanel buttons = new JPanel();
        buttons.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));

        if(cond!=null){
            JTextArea condText = new JTextArea(
                    ProofSaver.printTerm(cond, services, true).toString());
            buttons.add(condText);
            
            //      create "-->" button
            JButton sButton = new JButton("-->");
            sButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    successful = true;
                    spec = (OperationContract) specList.getSelectedValue();
                    compare = 1;
                    setVisible(false);
                }
            });
            buttons.add(sButton);
            
            //      create "<--" button
            JButton wButton = new JButton("<--");
            wButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    successful = true;
                    spec = (OperationContract) specList.getSelectedValue();
                    compare = -1;
                    setVisible(false);
                }
            });
            buttons.add(wButton);
            
            getRootPane().setDefaultButton(sButton);
    
            final JTextArea selectedText = 
                new JTextArea(((OperationContract) 
                        specs.get(specList.getSelectedIndex())).getPre(
                                ((IWorkingSpaceOp) wso.op()).getSelf(wso), 
                                ((IWorkingSpaceOp) wso.op()).getParameters(wso), services).toString());
            buttons.add(selectedText);
            
            specList.addListSelectionListener(new ListSelectionListener(){
               public void valueChanged(ListSelectionEvent e){
                   selectedText.setText(((OperationContract) 
                           specs.get(specList.getSelectedIndex())).getPre(
                                   ((IWorkingSpaceOp) wso.op()).getSelf(wso), 
                                   ((IWorkingSpaceOp) wso.op()).getParameters(wso), services).toString());
               }
            });
        }else{
            JButton okButton = new JButton("Ok");
            okButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    successful = true;
                    spec = (OperationContract) specList.getSelectedValue();
                    compare = 0;
                    setVisible(false);
                }
            });
            buttons.add(okButton);
        }
        
        //create "cancel" button
        JButton cancelButton = new JButton("Cancel");
        cancelButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                spec = null;
                setVisible(false);
            }
        });
        buttons.add(cancelButton);

     

        getContentPane().setLayout(new BoxLayout(getContentPane(), 
                                                 BoxLayout.Y_AXIS));
        getContentPane().add(listPanel);
        
        getContentPane().add(buttons);
               
        pack();
        setVisible(true);
    }
    
    public OperationContract getOperationContract() {        
        return spec;
    }
    
    public int compare(){
        return compare;
    }
    
    public boolean wasSuccessful() {
        return successful;
    }
    
    class PreCondRenderer extends JTextArea implements ListCellRenderer
    {

        public PreCondRenderer()
        {
            setLineWrap(false);
            setWrapStyleWord(false);
        }


        public Component getListCellRendererComponent(JList list, Object value,
            int index, boolean isSelected, boolean cellHasFocus)
        {
            setText(((OperationContract) value).getPre(
                    ((IWorkingSpaceOp) wso.op()).getSelf(wso), 
                    ((IWorkingSpaceOp) wso.op()).getParameters(wso), services).toString());       
          
            setBackground(isSelected ? Color.CYAN : Color.WHITE);
            return this;
        }
    }
        
}
