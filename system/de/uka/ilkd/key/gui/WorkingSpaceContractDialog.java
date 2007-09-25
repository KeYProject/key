package de.uka.ilkd.key.gui;

import java.awt.Color;
import java.awt.Component;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.LinkedList;
import java.util.Vector;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.ListCellRenderer;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.jml.JMLMethodSpec;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.ProofSaver;

public class WorkingSpaceContractDialog extends JDialog {

    LinkedList specs;
    boolean successful;
    JMLMethodSpec spec;
    int compare=1;
    Term cond;
    final Services services;
    
    public WorkingSpaceContractDialog(String title, JFrame parent, 
            Services services) {
        super(parent, title, true);
        this.services = services;
    }
    
    public void setSpecifications(LinkedList specs){
        this.specs = specs;
    }
    
    public void setCondition(Term cond){
        this.cond = cond;
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
                    spec = (JMLMethodSpec) specList.getSelectedValue();
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
                    spec = (JMLMethodSpec) specList.getSelectedValue();
                    compare = -1;
                    setVisible(false);
                }
            });
            buttons.add(wButton);
            
            getRootPane().setDefaultButton(sButton);
    
            final JTextArea selectedText = 
                new JTextArea(ProofSaver.printTerm(((JMLMethodSpec) 
                        specs.get(specList.getSelectedIndex())).
                        getPre(), services, true).toString());
            buttons.add(selectedText);
            
            specList.addListSelectionListener(new ListSelectionListener(){
               public void valueChanged(ListSelectionEvent e){
                   selectedText.setText(ProofSaver.printTerm(((JMLMethodSpec) 
                           specs.get(specList.getSelectedIndex())).
                           getPre(), services, true).toString());
               }
            });
        }else{
            JButton okButton = new JButton("Ok");
            okButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    successful = true;
                    spec = (JMLMethodSpec) specList.getSelectedValue();
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
    
    public JMLMethodSpec getMethodSpec() {        
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
            setText(ProofSaver.printTerm(((JMLMethodSpec) value).getPre(),
                    services, true).toString());       
          
            setBackground(isSelected ? Color.CYAN : Color.WHITE);
            return this;
        }
    }
        
}
