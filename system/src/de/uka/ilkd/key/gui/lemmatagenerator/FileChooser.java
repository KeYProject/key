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
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.ScrollPaneConstants;

import de.uka.ilkd.key.gui.KeYFileChooser;



public class FileChooser extends JPanel{
        private static final long serialVersionUID = 1L;
        private static final String HELP_TEXT = 
                "In this dialog you can choose the files that are used for loading user-defined taclets:\n\n" +
                "User-Defined Taclets:\nThis file contains the taclets that should be loaded, so that they can be used " +
                "for the current proof. For each taclet an extra proof obligation is built that must be provable, in order" +
                " to sustain the correctness of the calculus.\n" +
                "\nDefinitions:\n" +
                "This file contains the defintions (function symbols, predicate symbols, sorts)" +
                " that are used for creating the proof obligations mentioned above. In most cases it should be the same file" +
                " as indicated in 'User-Defined Taclets'.\n" +
                "\nAxioms:\nIn order to prove the correctness of the created lemmata," +
                " for some user-defined taclets the introduction " +
                "of additional axioms is necessary. At this point you can add them.\n" +
                "Beware of the fact that it is crucial for the correctness of the calculus that the used axioms are consistent." +
                "It is the responsibility of the user to guarantee this consistency.\n\n" +
                "Technical Remarks:\nThe axioms must be stored in another file than the user-defined taclets. Furthermore the axioms " +
                "are only loaded for the lemmata, but not for the current proof.";

        private class SingleFileChooser extends Box{
                private static final long serialVersionUID = 1L;
                private File           chosenFile;
                private JButton    chooseFileButton;
                private JTextField fileField;
                public SingleFileChooser(String title) {
                        super(BoxLayout.X_AXIS);
                        this.setBorder(BorderFactory.createTitledBorder(title));
                        this.add(getFileField());
                        this.add(Box.createHorizontalStrut(5));
                        this.add(getChooseFileButton());
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
                                                File file = chooseFiles("File containing the lemmata.");
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
        
        private boolean       closedByOkayButton = false;
        private final DefaultListModel listModel = new DefaultListModel();
        private static final Dimension MAX_DIM = new Dimension(Integer.MAX_VALUE,Integer.MAX_VALUE);
              
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
                        lemmataFileChooser = new SingleFileChooser("User-Defined Taclets"){
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
                                };
                        };
                        
                }
               return lemmataFileChooser;
        }
        
        private SingleFileChooser getDefinitionFileChooser(){
                if(definitionFileChooser == null){
                        definitionFileChooser = new SingleFileChooser("Definitions");
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
                      okayButton  = new JButton("OK"); 
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
        
        
        
}