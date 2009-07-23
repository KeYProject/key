// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Set;

import javax.swing.*;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.configuration.GeneralSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.AbstractEnvInput;
import de.uka.ilkd.key.proof.init.ModStrategy;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.jml.JMLSpecExtractor;


/** 
 * EnvInput for standalone specification language front ends.
 */
public class SLEnvInput extends AbstractEnvInput {
        
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    private static String getLanguage() {
        GeneralSettings gs 
            = ProofSettings.DEFAULT_SETTINGS.getGeneralSettings();
        if(gs.useJML() && gs.useOCL()) {
            return "JML/OCL";
        } else if(gs.useJML()) {
            return "JML";
        } else if(gs.useOCL()) {
            return "OCL";
        } else {
            return "no";
        }
    }
    
    
    public SLEnvInput(String javaPath) {
        super(getLanguage() + " specifications", javaPath);
        assert javaPath != null;
    }
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private KeYJavaType[] sortKJTs(KeYJavaType[] kjts) {
        
        Arrays.sort(kjts, new Comparator<KeYJavaType> () {
            public int compare(KeYJavaType o1, KeYJavaType o2) {
                return o1.getFullName().compareTo(o2.getFullName());
            }
        });
        
        return kjts;
    }
    
    
    private void showWarningDialog(SetOfPositionedString warnings) {
        if(!Main.visible) {
            return;
        }
                
        final JDialog dialog = new JDialog(Main.getInstance(), 
                                           getLanguage() + " warning", 
                                           true);
        dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        Container pane = dialog.getContentPane();
        pane.setLayout(new BorderLayout());
        
        //top label
        JLabel label = new JLabel("The following non-fatal "
                                  + "problems occurred when translating your " 
                                  + getLanguage() + " specifications:");
        label.setBorder(BorderFactory.createEmptyBorder(5, 5, 0, 5));
        pane.add(label, BorderLayout.NORTH);
          
        //scrollable warning list
        JScrollPane scrollpane = new JScrollPane();
        scrollpane.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        JList list = new JList(warnings.toArray());
        list.setBorder(BorderFactory.createLoweredBevelBorder());
        scrollpane.setViewportView(list);
        pane.add(scrollpane, BorderLayout.CENTER);
    
        //ok button
        final JButton button = new JButton("OK");
        button.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                dialog.setVisible(false);
                dialog.dispose();
            }
        });
        Dimension buttonDim = new Dimension(100, 27);
        button.setPreferredSize(buttonDim);
        button.setMinimumSize(buttonDim);
        JPanel panel = new JPanel();
        panel.add(button);
        pane.add(panel, BorderLayout.SOUTH);
        dialog.getRootPane().setDefaultButton(button);
        
        button.registerKeyboardAction(
            new ActionListener() {
                public void actionPerformed(ActionEvent event) {
                    if(event.getActionCommand().equals("ESC")) {
                        button.doClick();
                    }
                }
            },
            "ESC",
            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
            JComponent.WHEN_IN_FOCUSED_WINDOW);
        
        dialog.setSize(700, 300);
        dialog.setLocationRelativeTo(Main.getInstance());
        dialog.setVisible(true);
    }
    
    
    private void createSpecs(SpecExtractor specExtractor) 
            throws ProofInputException {
        JavaInfo javaInfo 
            = initConfig.getServices().getJavaInfo();
        SpecificationRepository specRepos 
            = initConfig.getServices().getSpecificationRepository();
       
        //sort types alphabetically (necessary for deterministic names)
        final Set<KeYJavaType> allKeYJavaTypes = javaInfo.getAllKeYJavaTypes();
        for (KeYJavaType keYJavaType : allKeYJavaTypes) {
            if(keYJavaType.getJavaType() == null) {
                System.out.println(keYJavaType);
            }
        }
        final KeYJavaType[] kjts = 
            sortKJTs(allKeYJavaTypes.toArray(new KeYJavaType[allKeYJavaTypes.size()]));
        
        //create specifications for all types
        for(KeYJavaType kjt : kjts) {
            //class invariants
            specRepos.addClassInvariants(
                        specExtractor.extractClassInvariants(kjt));
            
            //contracts, loop invariants
            ListOfProgramMethod pms 
                = javaInfo.getAllProgramMethodsLocallyDeclared(kjt);
            for(ProgramMethod pm : pms) {
                //contracts
                specRepos.addOperationContracts(
                            specExtractor.extractOperationContracts(pm));
                
                //loop invariants
                JavaASTCollector collector 
                    = new JavaASTCollector(pm.getBody(), LoopStatement.class);
                collector.start();
                for(ProgramElement loop : collector.getNodes()) {
                    LoopInvariant inv = specExtractor.extractLoopInvariant(
                	    			pm, 
                        			(LoopStatement) loop);
                    if(inv != null) {
                        specRepos.setLoopInvariant(inv);
                    }
                }
            }
        }
        
        //show warnings to user
        SetOfPositionedString warnings = specExtractor.getWarnings();
        if(warnings != null && warnings.size() > 0) {
            showWarningDialog(warnings);
        }
    }

    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public void read(ModStrategy mod) throws ProofInputException {
        if(initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
        
        GeneralSettings gs 
            = ProofSettings.DEFAULT_SETTINGS.getGeneralSettings();
        if(gs.useJML()) {
            createSpecs(new JMLSpecExtractor(initConfig.getServices()));
        }
    }
}
