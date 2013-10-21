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

package de.uka.ilkd.key.gui.smt;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;



import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTree;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.gui.IconFactory;



class OptionContentNode extends DefaultMutableTreeNode{
        private static final long serialVersionUID = 1L;
        private final JComponent component;
        
       
        public OptionContentNode(String title,JComponent component) {
                super();
                this.component = component;
                this.setUserObject(title);
        }

        public JComponent getComponent(){
                return component;
        }
                
}

public class SettingsDialog extends JDialog{
        private static final long serialVersionUID = 1L;
        public static final int APPLY_BUTTON =0;
        public static final int CANCEL_BUTTON =1;

        public static final int OKAY_BUTTON =3;
        private JTree optionTree;
        private JSplitPane splitPane;
        private JPanel optionPanel;
        private JButton applyButton;
        private JButton okayButton;
        private JButton cancelButton;

        private final ActionListener listener;
        private final ActionListener buttonListener = new ActionListener() {
                
                @Override
                public void actionPerformed(ActionEvent e) {
                        ActionEvent action = null;
                       if(e.getSource() == getApplyButton()){
                               action = new ActionEvent(SettingsDialog.this,APPLY_BUTTON,"pushed");
                       }
                       if(e.getSource() == getCancelButton()){
                               action = new ActionEvent(SettingsDialog.this,CANCEL_BUTTON,"pushed");
                       }
                       if(e.getSource() == getOkayButton()){
                               action = new ActionEvent(SettingsDialog.this,OKAY_BUTTON,"pushed");
                       }

                       if(action != null){
                               listener.actionPerformed(action);
                       }
                        
                }
        };
        
        
        public  SettingsDialog(TreeModel model, JComponent startComponent, ActionListener listener, JComponent bottomComponent){
                this.listener = listener;
                this.getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
                Box box = Box.createHorizontalBox();
                box.add(getSplitPane());
                this.getContentPane().add(box);
                this.getContentPane().add(Box.createVerticalStrut(5));
                box = Box.createHorizontalBox();
                box.add(Box.createHorizontalStrut(5));
                box.add(bottomComponent);
                box.add(Box.createHorizontalStrut(5));
                box.add(Box.createHorizontalGlue());
                box.add(getApplyButton());
                box.add(Box.createHorizontalStrut(5));
                box.add(getOkayButton());
                box.add(Box.createHorizontalStrut(5));
                box.add(getCancelButton());
                box.add(Box.createHorizontalStrut(5));
                this.getContentPane().add(box);
                this.getOptionTree().setModel(model);
                getSplitPane().setRightComponent(startComponent);
          
                this.getOptionTree().getParent().setMinimumSize(getOptionTree().getPreferredSize());
                this.getContentPane().setPreferredSize(computePreferredSize(model));
                this.setLocationByPlatform(true);
                this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
                setIconImage(IconFactory.keyLogo());
                this.pack();
                
        }
        
        private Dimension computePreferredSize(TreeModel model){
                DefaultMutableTreeNode node = (DefaultMutableTreeNode)model.getRoot();
                Dimension dim = computePreferredSize(node);
                dim.width = dim.width + getOptionTree().getPreferredSize().width+80;
                dim.height = Math.min(dim.height,400);
                return dim;
        }
        
        private Dimension computePreferredSize(DefaultMutableTreeNode node){
                
                Dimension dim = node instanceof OptionContentNode ? new Dimension(((OptionContentNode)node).getComponent().getPreferredSize()) : new Dimension(0,0);
                                
                for(int i=0; i<node.getChildCount(); i++){
                            Dimension dimChild = computePreferredSize((DefaultMutableTreeNode)node.getChildAt(i));
                            dim.width = Math.max(dimChild.width,dim.width);
                            dim.height = Math.max(dimChild.height,dim.height);
                        
                }
                return dim;
        }
        
        
        private JTree getOptionTree(){
                if(optionTree == null){
                        optionTree = new JTree();  
                        optionTree.addTreeSelectionListener(new TreeSelectionListener() {
                            
                            @Override
                            public void valueChanged(TreeSelectionEvent e) {
                                TreePath path = e.getNewLeadSelectionPath();
                                        
                                        if (path != null) {
                                                Object node = path.getLastPathComponent();
                                                if (node != null && node instanceof OptionContentNode) {
                                                        getSplitPane().setRightComponent(((OptionContentNode)node).getComponent());
                                          
                                                }
                                        }
                            }
                        });
                }
                return optionTree;
        }
        
        private JSplitPane getSplitPane(){
                if(splitPane == null){
                        
                        splitPane = new JSplitPane();
                        splitPane.setAlignmentX(LEFT_ALIGNMENT);
                        splitPane.setLeftComponent(new JScrollPane(getOptionTree()));
                        splitPane.setRightComponent(getOptionPanel());
                        //splitPane.setResizeWeight(0.2);
                }
                return splitPane;
                
        }
        
        private JPanel getOptionPanel(){
                if(optionPanel == null){
                        optionPanel = new JPanel();
                }
                return optionPanel;
        }
        
        public JButton getOkayButton() {
                if(okayButton == null){
                        okayButton = new JButton("Okay");
                        okayButton.addActionListener(buttonListener);
                }
                return okayButton;
        }
        
        public JButton getCancelButton() {
                if(cancelButton == null){
                        cancelButton = new JButton("Cancel");
                        cancelButton.addActionListener(buttonListener);
                }
                return cancelButton;
        }
        
        public JButton getApplyButton() {
                if(applyButton == null){
                        applyButton = new JButton("Apply");
                        applyButton.addActionListener(buttonListener);
                }
                return applyButton;
        }
        

        
        

        
}