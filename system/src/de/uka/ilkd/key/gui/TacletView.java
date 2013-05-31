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


/**
 * @author koenn
 *
 */
package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Dialog.ModalityType;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;

import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.Taclet;

@Deprecated
public class TacletView implements ActionListener{

    private JDialog frame;
    private JTextArea content;
    private JScrollPane scrollPane;

    private static TacletView instance = null;


    public static TacletView getInstance() {
        if (instance == null) {
            instance = new TacletView();
        }
        return instance;
    }
    

    private TacletView() {

        frame = new JDialog(MainWindow.getInstance());
        frame.setTitle("Taclet View");
        frame.setLocationByPlatform(true);

        frame.getContentPane().setLayout(new BorderLayout());

        content = new JTextArea("", 15, 30);       
        content.setEditable(false);
        content.setLineWrap(true);
        content.setWrapStyleWord(true);

        scrollPane = new JScrollPane(content,
                ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

        scrollPane.setWheelScrollingEnabled(true);

        scrollPane.setBorder(BorderFactory.createTitledBorder("Taclet"));	             

        JButton button = new JButton("Close");
        button.addActionListener(this);

        JPanel buttonPane = new JPanel();           
        buttonPane.add(button);

        frame.getContentPane().add(scrollPane, BorderLayout.CENTER);
        frame.getContentPane().add(buttonPane, BorderLayout.SOUTH);
        
        frame.getRootPane().setDefaultButton(button);

        frame.pack();	   
    }

    
    public void actionPerformed(ActionEvent e){
        frame.setVisible(false);
    }
    
    
    public void showTacletView(Taclet tac, boolean modal){
        frame.setModalityType(modal? 
                ModalityType.APPLICATION_MODAL: ModalityType.MODELESS);
        scrollPane.setBorder(BorderFactory.createTitledBorder
                (getDisplayName(tac)));
        content.setText(getTacletByName(tac));

        content.setCaretPosition(0);

        frame.validate();
        frame.setVisible(true);	
    }

    
    public void showTacletView(DefaultMutableTreeNode node){
        if (node.getUserObject() instanceof Taclet) {
            Taclet tac = (Taclet) node.getUserObject();
            showTacletView(tac, false);
        } 
    }

    
    private String getDisplayName(Taclet tac){
        return tac.displayName();
    }


    private String getTacletByName(Taclet tac){
        String rule;
        LogicPrinter lp = 
            new LogicPrinter(new ProgramPrinter(), new NotationInfo(), null, true);
        lp.printTaclet(tac);
        rule = lp.toString();

        return rule;
    }
}
