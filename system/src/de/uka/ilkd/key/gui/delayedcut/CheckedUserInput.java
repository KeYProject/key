package de.uka.ilkd.key.gui.delayedcut;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.LinkedList;
import java.util.List;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextPane;
import javax.swing.SwingUtilities;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

public class CheckedUserInput extends JPanel{
    private static final long serialVersionUID = 1L;



    static public interface CheckedUserInputInspector{
        public boolean check(String toBeChecked);
    }
    
    static public interface CheckedUserInputListener{
        public void userInputChanged(String input,boolean valid);
      
    }
   
    
    private TrafficLight trafficLight;
    private JTextPane    inputFieldForFormula;
    

    private final CheckedUserInputInspector inspector; 
    private final List<CheckedUserInputListener> listeners = new LinkedList<CheckedUserInputListener>();
    
    public CheckedUserInput(CheckedUserInputInspector inspector) {
        this.inspector = inspector;
        this.setLayout(new BoxLayout(this,BoxLayout.X_AXIS));
        this.add(new JScrollPane(getInputFieldForFormula()));
        this.add(Box.createHorizontalStrut(5));
        this.add(getTrafficLight());
    }

    
    private TrafficLight getTrafficLight(){
        if(trafficLight == null) {
            trafficLight = new TrafficLight(10);            
        }
        return trafficLight;
    }
    
    private JTextPane getInputFieldForFormula(){
        if(inputFieldForFormula == null){
                inputFieldForFormula = new JTextPane();
                inputFieldForFormula.getDocument().addDocumentListener(new DocumentListener() {
                                    
                 @Override
                 public void removeUpdate(DocumentEvent e) {
                      checkInput();  
                         
                 }                 
                 @Override
                 public void insertUpdate(DocumentEvent e) {
                       checkInput();
                         
                 }                 
                 @Override
                 public void changedUpdate(DocumentEvent e) {
                        
                 }
         });
                
        }
        return inputFieldForFormula;
}
    
    private void checkInput(){
        String text = inputFieldForFormula.getText();
        boolean result = inspector.check(text);
        setValid(result);
        for(CheckedUserInputListener listener : listeners){
            listener.userInputChanged(text,result);
        }
    }
    
    public void addListener(CheckedUserInputListener listener){
        listeners.add(listener);
    }
    

    public void removeListener(CheckedUserInputListener listener){
        listeners.remove(listener);
    }
    
    public String getInput(){
        return getInputFieldForFormula().getText();
    }
    
    public void setInput(String input){
        getInputFieldForFormula().setText((input == null) ? "" : input);
        checkInput();
    }

private void setValid(boolean b){
        getTrafficLight().setGreen(b);
        SwingUtilities.invokeLater(new Runnable() {
         
         @Override
         public void run() {
                 getTrafficLight().repaint();
         }
        });
}
    
    public static String showAsDialog(String title,String description,
                                        final String helpText,
                                        String defaultInput,
                                       CheckedUserInputInspector inspector
                                       
                                       ) {
        CheckedUserInput userInput = new CheckedUserInput(inspector);
        
        Box vertBox = Box.createVerticalBox();
        if(description != null){
            Box horzBox = Box.createHorizontalBox();
            horzBox.add(new JLabel(description));
            horzBox.add(Box.createHorizontalGlue());
            vertBox.add(horzBox);
            vertBox.add(Box.createVerticalStrut(5));
        }
        vertBox.add(userInput);
        final StdDialog dialog = new StdDialog(title,
                vertBox, 5, helpText!= null);
        userInput.addListener(new CheckedUserInputListener(){

            @Override
            public void userInputChanged(String input, boolean valid) {
               dialog.getOkayButton().setEnabled(valid);                
            }            
        });

        dialog.getHelpButton().addActionListener(new ActionListener() {
            
            @Override
            public void actionPerformed(ActionEvent e) {
               JOptionPane.showMessageDialog(dialog, helpText,"Help" ,
                       JOptionPane.INFORMATION_MESSAGE);
            }
        });
        
        userInput.setInput(defaultInput);
        
        dialog.setVisible(true);
        
        if(dialog.okayButtonHasBeenPressed()){
            return userInput.getInput();
        }
        return null;  
    }
    
    
    
    public static void main(String [] args){
        showAsDialog("Test","description","that is only a test","default",
                new CheckedUserInputInspector() {
            
            @Override
            public boolean check(String toBeChecked) {

                return toBeChecked.equals("test");
            }
        });
    }
}
