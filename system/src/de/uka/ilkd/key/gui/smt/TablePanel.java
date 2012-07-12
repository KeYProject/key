package de.uka.ilkd.key.gui.smt;


import java.awt.Dimension;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;


public abstract class TablePanel extends JPanel{
        private static final long serialVersionUID = 1L;
        private static final int STRUT = 5;
        
        private JTextArea infoText;
        
        protected  TablePanel() {
                this.setLayout(new BoxLayout(this,BoxLayout.Y_AXIS));
       
        }
        
        protected void updateOptions(){};
        
        protected final void createTable(){
                createComponents();
                finalizeAddingComponents();
        }
        
        private void addInfo(JButton infoButton, String info){
         
                final JTextArea infoBox = addInfoArea(info);
               
                infoBox.setVisible(false);
            
                infoButton.addActionListener(new ActionListener() {
                        
                        @Override
                        public void actionPerformed(ActionEvent e) {
                                infoBox.setVisible(!infoBox.isVisible());
                        }
                });           
        }
        
        protected JTextArea addInfoArea(String info){
                JTextArea textArea = new JTextArea(info);
                textArea.setBackground(this.getBackground());
                textArea.setEditable(false);
                textArea.setLineWrap(true);
                textArea.setWrapStyleWord(true);
                addComponent(null,textArea);
                return textArea;
        }
        
        protected Box addComponent(String info,JComponent ... components){
                Box box = Box.createHorizontalBox();
                for(JComponent component : components){
                	component.setAlignmentX(LEFT_ALIGNMENT);
                	box.add(Box.createHorizontalStrut(STRUT));
                	box.add(component);                
                }
                box.add(Box.createHorizontalStrut(STRUT));
                JButton infoButton = null;
                if(info != null && info != "" ){
                    infoButton = new JButton("?");
                    box.add(Box.createHorizontalGlue());
                    box.add(infoButton);
                    box.add(Box.createHorizontalStrut(STRUT));
                }
                this.add(Box.createVerticalStrut(STRUT));
                this.add(box);
                if(infoButton != null){
                       addInfo(infoButton,info);
                }
                return box;
        }
        
        protected JCheckBox createCheckBox(String title, boolean value, ActionListener changeListener){
                JCheckBox checkBox = new JCheckBox(title,value);
                checkBox.addActionListener(changeListener);
                return checkBox;
        }
        
        protected JCheckBox addCheckBox(String title, String info, boolean value, ActionListener changeListener){
                JCheckBox checkBox = createCheckBox(title, value, changeListener);
                addComponent(info,checkBox);
                return checkBox;
        }
        

        
        protected FileChooserPanel addFileChooserPanel(String title, String file, String info,
                        boolean selected,boolean enabled, ActionListener changeListener){
              FileChooserPanel fileChooserPanel =  new FileChooserPanel(selected,enabled,title);
              fileChooserPanel.addActionListener(changeListener);
              setMaximumHeight(fileChooserPanel, fileChooserPanel.getPreferredSize().height);
              addComponent(info,fileChooserPanel);
              
              return fileChooserPanel;
        }
        
        protected JComboBox addComboBox(String info,int selectionIndex,ActionListener changeListener,Object... items){
                JComboBox comboBox = new JComboBox(items);
                comboBox.setSelectedIndex(selectionIndex);
                comboBox.addActionListener(changeListener);
                addComponent(info,comboBox);
                return comboBox;
        }
        
        private void setMaximumHeight(JComponent component, int height){
                Dimension dim = component.getMaximumSize();
                dim.height = height;
                component.setMaximumSize(dim);
        }
        
        protected JTextField createTextField(String text ,final ActionListener changeListener){
                JTextField field = new JTextField(text);
                field.getDocument().addDocumentListener(new DocumentListener() {
                        
                        @Override
                        public void removeUpdate(DocumentEvent e) {if(changeListener != null)changeListener.actionPerformed(null);}
                        
                        @Override
                        public void insertUpdate(DocumentEvent e) {if(changeListener != null)changeListener.actionPerformed(null);}
                        
                        @Override
                        public void changedUpdate(DocumentEvent e) {if(changeListener != null)changeListener.actionPerformed(null);}
                });
                return field;
        }
        
        protected Box createTitledComponent(String title,int minWidthOfTitle, JComponent component){
                Box box = Box.createHorizontalBox();
                JLabel label = new JLabel(title);
                Dimension dim = label.getMinimumSize();
                dim.width = minWidthOfTitle;
                label.setMinimumSize(dim);
                dim = label.getPreferredSize();
                dim.width = minWidthOfTitle;
                label.setPreferredSize(dim);
                box.add(label);
                box.add(Box.createHorizontalStrut(5));
                box.add(Box.createHorizontalGlue());
                box.add(component);
                setMaximumHeight(box, component.getPreferredSize().height);
                return box;
        }
        
        protected JTextField addTextField(String title,int minWidthOfTitle, String text, String info,final ActionListener changeListener){
                JTextField field = createTextField( text, changeListener);
                Box box = createTitledComponent(title,minWidthOfTitle, field);
        
                addComponent(info,box);
                
                return field;              
        }
        
        
        
        public JTextArea getInfoText() {
                 return infoText;
        }
        
        final protected void finalizeAddingComponents(){
             infoText = addInfoArea("");
        }
        
        abstract protected void createComponents();
        
}



