//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//Universitaet Koblenz-Landau, Germany
//Chalmers University of Technology, Sweden

//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.

/*
 * Created on 09.09.2004
 */
/**
 * @author koenn
 *
 */

package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;

import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.rule.Taclet;

public class TacletView implements ActionListener{

    private JFrame frame;
    private JTextArea content;
    private JScrollPane scrollPane;

    private static TacletView instance = null;


    public static TacletView getInstance() {
        if (instance == null) {
            instance = new TacletView();
        }
        return instance;
    }

    private TacletView(){

        frame = new JFrame("Taclet View");	    	            

        frame.getContentPane().setLayout(new BorderLayout());

        content = new JTextArea("", 15, 30);       
        content.setEditable(false);
        content.setLineWrap(true);
        content.setWrapStyleWord(true);

        scrollPane = new JScrollPane(content,
                JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
                JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);

        scrollPane.setWheelScrollingEnabled(true);

        scrollPane.setBorder(BorderFactory.createTitledBorder("Taclet"));	             

        JButton button = new JButton("Close");
        button.addActionListener(this);

        JPanel buttonPane = new JPanel();           
        buttonPane.add(button);

        frame.getContentPane().add(scrollPane, BorderLayout.CENTER);
        frame.getContentPane().add(buttonPane, BorderLayout.SOUTH);

        frame.pack();	   
    }

    public void actionPerformed(ActionEvent e){
        frame.setVisible(false);
    }

    public void showTacletView(DefaultMutableTreeNode node){
        Taclet tac = null;
        if (node.getUserObject() instanceof Taclet) {
            tac = (Taclet) node.getUserObject();        
        } else if (node.getUserObject() instanceof Contract) {
            tac = null; //TODO ((Contract)node.getUserObject()).getLemmaAndRegister();
        } else return;
        scrollPane.setBorder(BorderFactory.createTitledBorder
                (getDisplayName(tac)));
        content.setText(getTacletByName(tac));

        content.setCaretPosition(0);

        frame.validate();
        frame.setVisible(true);	
    }

    private String getDisplayName(Taclet tac){
        String title = tac.displayName();	   
        return title;
    }


    private String getTacletByName(Taclet tac){
        String rule = "";
        LogicPrinter lp = 
            new LogicPrinter(new ProgramPrinter(), new NotationInfo(), null, true);
        lp.printTaclet(tac);
        rule = lp.toString();

        return rule;
    }
}
