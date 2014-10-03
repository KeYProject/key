// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.lemmatagenerator;

import java.awt.Component;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.LinkedList;
import java.util.List;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.ScrollPaneConstants;
import javax.swing.WindowConstants;

import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;



public class FileChooser extends JPanel{
        private static final long serialVersionUID = 1L;
        private static final String HELP_TEXT = 
                "In this dialog you can choose the files that are used for loading user-defined taclets:\n\n" +
                "User-Defined Taclets:\nThis file contains the taclets that should be loaded, so that they can be used " +
                "for the current proof. For each taclet an extra proof obligation is built that must be provable, in order" +
                " to sustain the correctness of the calculus.\n" +
                "\nDefinitions:\n" +
                "This file contains the signature (function symbols, predicate symbols, sorts)" +
                " that are used for creating the proof obligations mentioned above. In most cases it should be the same file" +
                " as indicated in 'User-Defined Taclets'.\n" +
                "\nAxioms:\nIn order to prove the correctness of the created lemmata," +
                " for some user-defined taclets the introduction " +
                "of additional axioms is necessary. At this point you can add them.\n" +
                "Beware of the fact that it is crucial for the correctness of the calculus that the used axioms are consistent." +
                "It is the responsibility of the user to guarantee this consistency.\n\n" +
                "Technical Remarks:\nThe axioms must be stored in another file than the user-defined taclets. Furthermore the axioms " +
                "are only loaded for the lemmata, but not for the current proof.";
        
        private static final String INFO_TEXT1 = "Be aware of the fact that you are going to load taclets\n" +
        		                                    "without creating corresponding proof obligations!\n"+
        		                                    "In case that the taclets that you want to load are unsound,\n"+
        		                                    "the calculus will become unsound!";
        private static final String INFO_TEXT2 = "Be aware of the fact that you are going to load taclets\n" +
        		                                    "without creating corresponding proof obligations!\n"+
        		                                    "In case that the taclets that you want to load are unsound,\n"+
        		                                    "the calculus will become unsound!";
        
        
        private class SingleFileChooser extends Box{
                private static final long serialVersionUID = 1L;
                private File           chosenFile;
                private JButton    chooseFileButton;
                private JTextField fileField;
                private String title;
                
                
                
                public SingleFileChooser(String title, JCheckBox checkbox) {
           
                        super(BoxLayout.Y_AXIS);
                        this.title = title;
                        Box box = Box.createHorizontalBox();
                     
                        this.setBorder(BorderFactory.createTitledBorder(title));
                        
                      
                        box.add(getFileField());
                        box.add(Box.createHorizontalStrut(5));
                        box.add(getChooseFileButton());
                        this.add(box);
                        if(checkbox != null){
                                box = Box.createHorizontalBox();
                                box.add(getLemmaCheckBox());
                                box.add(Box.createHorizontalGlue());
                                this.add(Box.createVerticalStrut(5));
                                this.add(box);
                        }
                }
                
                private JTextField getFileField() {
                        if(fileField == null){
                                fileField = new JTextField();
                                setMaximumHeight(fileField, getChooseFileButton().getPreferredSize().height);
                                setMaximumWidth(fileField, Integer.MAX_VALUE);
                                fileField.setEditable(false);
                        }
                        return fileField;
                }
                
                private JButton getChooseFileButton() {
                        if(chooseFileButton == null){
                                chooseFileButton = new JButton("choose");
                                setMaximumWidth(chooseFileButton,getRemoveAxiomFileButton().getPreferredSize().width);
                                chooseFileButton.addActionListener(new ActionListener() {
                                        
                                        @Override
                                        public void actionPerformed(ActionEvent arg0) {
                                                File file = chooseFiles(title);
                                                if(file != null){
                                                        fileHasBeenChosen(file);
                                                        setChosenFile(file);
                                                      
                                                }
                                        }
                                });
                        }
                        return chooseFileButton;
                }   
                
                protected void fileHasBeenChosen(File file){
                        
                }
                
                public void setChosenFile(File file){
                        chosenFile = file;
                        getFileField().setText(chosenFile.toString());   
                }
                
                public File getChosenFile() {
                        return chosenFile;
                }
        }
        

        private JList      axiomsList;
        private JButton    addAxiomFileButton;
        private JButton    removeAxiomFileButton;
        private JButton    helpButton;
        private SingleFileChooser lemmataFileChooser;
        private SingleFileChooser definitionFileChooser;
        private JPanel     axiomFilePanel;
        private JPanel     buttonPanel;
        private JScrollPane scrollPane;
        private KeYFileChooser fileChooser;
        private JDialog     helpWindow;

        private JDialog        dialog;
        private JButton okayButton;
        private JButton cancelButton;
        
        private JCheckBox lemmaCheckbox;
        
        private boolean       closedByOkayButton = false;
        private final DefaultListModel listModel = new DefaultListModel();
        private static final Dimension MAX_DIM = new Dimension(Integer.MAX_VALUE,Integer.MAX_VALUE);
        private boolean firstTimeAddingAxioms = true;      
        public FileChooser(){
             this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
             
             
             JLabel label = new JLabel("Please choose the files that should be browsed for..."); 
             label.setAlignmentX(Component.LEFT_ALIGNMENT);
             setMaximumWidth(label, Integer.MAX_VALUE);
            
             this.add(Box.createVerticalStrut(15));
             this.add(label);
             this.add(Box.createVerticalStrut(15));
             this.add(getLemmataFileChooser());
  
             this.add(Box.createVerticalStrut(5));
             this.add(getDefinitionFileChooser());
             this.add(Box.createVerticalStrut(5));
             this.add(getAxiomFilePanel());
             this.add(Box.createVerticalGlue());
        }
        
        public List<File> getFilesForAxioms(){
                List<File> files = new LinkedList<File>();
                Object objects [] = listModel.toArray();
                if(objects != null){
                        for(Object file : objects){
                                files.add((File)file);
                        }
                }
                return files;
        }
        
        public File getFileForLemmata(){
                return lemmataFileChooser.getChosenFile();
        }
        
        public File getFileForDefinitions(){
                return definitionFileChooser.getChosenFile();
        }
        
        private JCheckBox getLemmaCheckBox(){
                if(lemmaCheckbox == null){
                        lemmaCheckbox = new JCheckBox("Load taclets as lemmata.");
                        lemmaCheckbox.setSelected(true);
                        lemmaCheckbox.addActionListener(new ActionListener() {
                                
                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        
                                        InfoDialog infoDialog = new InfoDialog();
                                        if(!lemmaCheckbox.isSelected()){
                                            lemmaCheckbox.setSelected(true);   
                                            boolean showDialogUsingAxioms = ProofIndependentSettings.DEFAULT_INSTANCE
                                            .getLemmaGeneratorSettings()
                                            .isShowingDialogUsingAxioms();
                                            if((showDialogUsingAxioms &&
                                                            infoDialog.showDialog(INFO_TEXT1,FileChooser.this)) || 
                                                            !showDialogUsingAxioms){
                                              changedToNotSelected();   
                                              lemmaCheckbox.setSelected(false);  
                                               ProofIndependentSettings.DEFAULT_INSTANCE
                                              .getLemmaGeneratorSettings()
                                              .showDialogUsingAxioms(showDialogUsingAxioms && infoDialog
                                                              .showThisDialogNextTime()  );
                                            }
                                        }else{
                                            changedToSelected();
                                        }
                                                                
                                }
                        });
                }
                return lemmaCheckbox;
        }
        
        private void enableAxiomFilePanel(boolean val){
                getAddAxiomFileButton().setEnabled(val);
                getRemoveAxiomFileButton().setEnabled(val);
                getAxiomsList().setEnabled(val);
        }
        
        private void changedToSelected(){
                enableAxiomFilePanel(true);
        }
        
        private void changedToNotSelected() {
                enableAxiomFilePanel(false);
        }

        
        
        private JList getAxiomsList() {
                if(axiomsList == null){
                        axiomsList = new JList();
                        axiomsList.setModel(listModel);
                        axiomsList.setBorder(BorderFactory.createEtchedBorder());
                }
                return axiomsList;
        }
        
        private KeYFileChooser getFileChooser(String title) {
           if (fileChooser == null) {
                    String initDir = System.getProperty("user.dir");
                    fileChooser = new KeYFileChooser(initDir);
                }
                fileChooser.setDialogTitle(title);
                fileChooser.prepare();
                return fileChooser;
       }
        
        private JButton getHelpButton(){
                if(helpButton == null){
                        helpButton = new JButton("Help");
                        helpButton.setPreferredSize(getCancelButton().getPreferredSize());
                        helpButton.addActionListener(new ActionListener() {
                                
                                @Override
                                public void actionPerformed(ActionEvent arg0) {
                                        getHelpWindow().setVisible(true);
                                }
                        });
                }
                return helpButton;
        }
        
        
        private JDialog getHelpWindow(){
              if(helpWindow == null){
                      helpWindow = dialog != null ?new JDialog(dialog) : new JDialog();
                      
                      JTextArea textArea = new JTextArea(HELP_TEXT);
                      textArea.setWrapStyleWord(true);
                      textArea.setLineWrap(true);
                      textArea.setEditable(false);
                      helpWindow.getContentPane().add(new JScrollPane(textArea));
                      helpWindow.setMinimumSize(new Dimension(400, 200));
                      helpWindow.setLocationByPlatform(true);
                      helpWindow.setTitle("Help");
                      helpWindow.pack();
                      
              }
              return helpWindow;
        }
        
    
        
        private JScrollPane getScrollPane(){
             if(scrollPane == null){
                     scrollPane = new JScrollPane(getAxiomsList(),ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
                                     ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
                     
                     scrollPane.setMaximumSize(MAX_DIM);
             }
             return scrollPane;
        }
        
        private File chooseFiles(String title){
                KeYFileChooser chooser = getFileChooser(title);
                chooser.showOpenDialog(this);
                
                return chooser.getSelectedFile();
        }

        private SingleFileChooser getLemmataFileChooser(){
                if(lemmataFileChooser == null){
                        lemmataFileChooser = new SingleFileChooser("User-Defined Taclets",getLemmaCheckBox()){
                                private static final long serialVersionUID = 1L;
                                protected void fileHasBeenChosen(File file) {
                                        if(okayButton != null){
                                                okayButton.setEnabled(true);
                                        }
                                        if(getDefinitionFileChooser().getChosenFile() == null ||
                                           getDefinitionFileChooser().getChosenFile() == 
                                           getLemmataFileChooser().getChosenFile()){
                                                getDefinitionFileChooser().setChosenFile(file);
                                        }
                                }
                        };
                        
                }
               return lemmataFileChooser;
        }
        
        private SingleFileChooser getDefinitionFileChooser(){
                if(definitionFileChooser == null){
                        definitionFileChooser = new SingleFileChooser("Signature",null);
                }
               return definitionFileChooser;
        }

        private JButton getAddAxiomFileButton() {
                if(addAxiomFileButton == null){
                    addAxiomFileButton = new JButton("add"); 
                    
                    setMaximumWidth(addAxiomFileButton,getRemoveAxiomFileButton().getPreferredSize().width);
                    addAxiomFileButton.addActionListener(new ActionListener() {
                        
                        @Override
                        public void actionPerformed(ActionEvent e) {
                               
                               if(firstTimeAddingAxioms && 
                                               ProofIndependentSettings.DEFAULT_INSTANCE.
                                               getLemmaGeneratorSettings().isShowingDialogAddingAxioms()){                                     
                                      
                                       InfoDialog infoDialog = new InfoDialog();
                                       firstTimeAddingAxioms = !infoDialog.showDialog(INFO_TEXT2,FileChooser.this);
                                       ProofIndependentSettings.DEFAULT_INSTANCE
                                       .getLemmaGeneratorSettings().showDialogAddingAxioms(infoDialog.showThisDialogNextTime());
                                       if(firstTimeAddingAxioms){
                                               return;
                                       }
                               }
                               File file = chooseFiles("File containing the axioms.");
                               if(file != null){
                                       listModel.addElement(file);
                                       
                               }
                        }
                });
                }
                return addAxiomFileButton;
        }

        private JButton getRemoveAxiomFileButton() {
                if(removeAxiomFileButton == null){
                        removeAxiomFileButton = new JButton("remove");
                        removeAxiomFileButton.addActionListener(new ActionListener() {
                                
                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        Object values[] = getAxiomsList().getSelectedValues();
                                        for(Object o : values){
                                                listModel.removeElement(o);
                                        }
                                        
                                }
                        });
                   
                }
                return removeAxiomFileButton;
        }
        
        private JPanel getAxiomFilePanel() {
                if(axiomFilePanel == null){
                        axiomFilePanel = new JPanel();
                        axiomFilePanel.setLayout(new BoxLayout(axiomFilePanel, BoxLayout.X_AXIS));
                       
                        axiomFilePanel.add(getScrollPane());
                        axiomFilePanel.add(Box.createHorizontalStrut(5));
                        axiomFilePanel.add(getButtonPanel());
                        axiomFilePanel.setBorder(BorderFactory.createTitledBorder("Axioms"));
                }
                return axiomFilePanel;
        }
        
        private JPanel getButtonPanel(){
                if(buttonPanel == null){
                        buttonPanel = new JPanel();
                        buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.Y_AXIS));
                        buttonPanel.add(Box.createVerticalGlue());
                        buttonPanel.add(getAddAxiomFileButton());
                        buttonPanel.add(Box.createVerticalStrut(5));
                        buttonPanel.add(getRemoveAxiomFileButton());
                        buttonPanel.add(Box.createVerticalGlue());
                }
                return buttonPanel;
        }
        

        
        private void setMaximumHeight(JComponent comp, int value){
                Dimension dim = comp.getMaximumSize();
                dim.height = value;
                comp.setMaximumSize(dim);
        }
        
        private void setMaximumWidth(JComponent comp, int value){
                Dimension dim = comp.getMaximumSize();
                dim.width = value;
                comp.setMaximumSize(dim);
        }
        
        private JDialog getDialog(){
                if(dialog == null){
                        dialog = new JDialog();
                        dialog.setTitle("Files for Loading User-Defined Taclets...");
                        dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
                        Container pane = dialog.getContentPane();
                
                        pane.setLayout(new BoxLayout(pane, BoxLayout.Y_AXIS));
                        
                        pane.add(this);
                        pane.add(Box.createVerticalStrut(5));
                        JPanel buttonPane = new JPanel();
                        buttonPane.setLayout(new BoxLayout(buttonPane, BoxLayout.X_AXIS));
                        buttonPane.add(getHelpButton());     
                        buttonPane.add(Box.createHorizontalGlue());
                        buttonPane.add(getOkayButton());
                        buttonPane.add(Box.createHorizontalStrut(10));
                        buttonPane.add(getCancelButton());
                        buttonPane.add(Box.createHorizontalStrut(5));
                        pane.add(buttonPane);
                        dialog.setLocationByPlatform(true);
                        dialog.pack();
                }
                return dialog;
        }
        
        private JButton getOkayButton(){
                if(okayButton == null){
                      okayButton  = new JButton("Okay"); 
                      Dimension dim = getCancelButton().getPreferredSize();
                      okayButton.setEnabled(false);
                      okayButton.setPreferredSize(dim);
                      okayButton.addActionListener(new ActionListener() {
                              @Override
                              public void actionPerformed(ActionEvent e) {
                                      getDialog().dispose();
                                      closedByOkayButton = true;
                              }
                            });   
                }
                return okayButton;
         }
        

        
        
        private JButton getCancelButton(){
                if(cancelButton == null){
                      cancelButton  = new JButton("Cancel");  
                      cancelButton.addActionListener(new ActionListener() {
                              @Override
                              public void actionPerformed(ActionEvent e) {
                                      getDialog().dispose();
                             
                              }
                            });   
                }
                return cancelButton;
         }
        
        
        public boolean showAsDialog(){
              
              getDialog().setModal(true);
              getDialog().setVisible(true);
              return closedByOkayButton;
        }
        
        public static void main(String [] args){
                FileChooser chooser = new FileChooser();
                chooser.showAsDialog();
        }
        
        public boolean isLoadingAsLemmata(){
                return this.getLemmaCheckBox().isSelected();
        }
        
        
        
}