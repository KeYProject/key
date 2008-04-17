// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.io.StringReader;

import javax.swing.*;

import de.uka.ilkd.key.logic.EverythingLocationDescriptor;
import de.uka.ilkd.key.logic.IteratorOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;


/**
 * A dialog for selecting / entering a depends clause.
 */
public class DependsClauseDialog extends JDialog {
    private static final int LINE_WIDTH = 70;
    
    private final InitConfig initConfig;
    private final SetOfLocationDescriptor defaultClause;
    private final JTextArea textArea;
    private SetOfLocationDescriptor currentClause;
    private boolean successful = false;


    public DependsClauseDialog(ClassInvariant inv,
                               InitConfig ic,
                               SetOfLocationDescriptor defaultClause) {
        super(new JFrame(),
              "Depends clause for \"" + inv 
              + "\"",
              true);
        this.initConfig    = ic;
        this.defaultClause = defaultClause;

        //create text area
        textArea = new JTextArea(10, LINE_WIDTH);
        setToDefault();
        JScrollPane scrollPane = new JScrollPane(textArea);
        getContentPane().add(scrollPane);

        //create button panel
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        getContentPane().add(buttonPanel);
        Dimension buttonDim = new Dimension(80, 25);

        //create "ok" button
        JButton okButton = new JButton("OK");
        okButton.setPreferredSize(buttonDim);
        okButton.setMinimumSize(buttonDim);
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                if(parseText()) {
                    successful = true;
                    setVisible(false);
                }
            }
        });
        buttonPanel.add(okButton);
        getRootPane().setDefaultButton(okButton);

        //create "restore default" button
        JButton restoreButton = new JButton("Restore default");
        Dimension restoreButtonDim = new Dimension(120, 25);
        restoreButton.setPreferredSize(restoreButtonDim);
        restoreButton.setMinimumSize(restoreButtonDim);
        restoreButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setToDefault();
            }
        });
        buttonPanel.add(restoreButton);

        getContentPane().setLayout(new BoxLayout(getContentPane(),
                                                 BoxLayout.Y_AXIS));
        pack();
        setLocation(70, 70);
        setVisible(true);
    }


    private void setToDefault() {
        currentClause = defaultClause;
        
        //print default clause to text area
        LogicPrinter printer 
            = new LogicPrinter(null, 
        	    	       NotationInfo.createInstance(), 
        	    	       initConfig.getServices());
        printer.setLineWidth(LINE_WIDTH);
        try {
            printer.printLocationDescriptors(defaultClause);
            textArea.setText(printer.toString());
        } catch(IOException e) {
            Debug.fail();
        }
    }


    private boolean parseText() {
        KeYLexer lexer
            = new KeYLexer(new StringReader(textArea.getText()),
                           initConfig.getServices().getExceptionHandler());
        KeYParser parser 
            = new KeYParser(ParserMode.TERM,
                            lexer,
                            null,
                            TermFactory.DEFAULT,
                            initConfig.getServices(),
                            initConfig.namespaces());
        try {
            SetOfLocationDescriptor locations = parser.location_list();
            
            //check for "*"-locations, which are not allowed here
            IteratorOfLocationDescriptor it = locations.iterator();
            while(it.hasNext()) {
                if(it.next() instanceof EverythingLocationDescriptor) {
                    throw new Exception(
                            "Please use a non-trivial depends clause.");
                }
            }
            
            currentClause = locations;
        } catch(Exception e) {
            ExtList list = new ExtList();
            list.add(e);
            new ExceptionDialog(this, list);
            return false;
        }

        return true;
    }


    /**
     * Tells whether the user clicked "ok".
     */
    public boolean wasSuccessful() {
        return successful;
    }


    public SetOfLocationDescriptor getDependsClause() {
        return currentClause;
    }
}
