package de.uka.ilkd.key.gui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;

import javax.swing.BoxLayout;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.unittest.TestExecuter;
import de.uka.ilkd.key.unittest.UnitTestBuilder;


public class TestExecutionDialog extends JDialog {
    
    static TestExecutionDialog tsw;
    final JFrame parent;
    public static final JList testList = new JList(new DefaultListModel());
    protected JTextArea classPathText; 
    /**The directory in which the commands "javac" and "java" are executed. */
    protected JTextField workingDirText = new JTextField();
    final static String COMPILE_ONLY_TEST="Compile only the test file and generated utility files (i.e. RFL.java)";
    final static String COMPILE_ALL="Compile all .java files in the test working directory and its sub-directories";
    protected JComboBox  compileChoice = new JComboBox(new String[]{COMPILE_ONLY_TEST,COMPILE_ALL});
    
    /**The first time this method is called the main frame must be provided as parameters.
     * In later calls the parameter is irrelevant. It may be null. */
    public static TestExecutionDialog getInstance(JFrame parent){
	if(tsw==null){
	    tsw = new TestExecutionDialog(parent);
	}
        tsw.pack();
	return tsw;
    }
    
    protected TestExecutionDialog(final JFrame parent){
	super(parent, "Select Test Case");
	this.parent = parent;
           getContentPane().setLayout(new BoxLayout(getContentPane(),BoxLayout.Y_AXIS));

           	testList.addListSelectionListener(new ListSelectionListener(){
           	    public void valueChanged(ListSelectionEvent e){
                        TestAndModel tam = (TestAndModel) testList.getSelectedValue();
                        //This is just a temporary solution. It is assumed that the test file is in the default package
                        //However, generally this is not correct
                        String workingDir = tam.test.substring(0, tam.test.lastIndexOf(File.separator));
                        workingDirText.setText(workingDir);
           	    }
           	});
               JScrollPane testListScroll = new
                   JScrollPane(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, 
                           ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
               testListScroll.getViewport().setView(testList);
               testListScroll.setBorder(new TitledBorder("Created Tests"));
               testListScroll.setMinimumSize(new java.awt.Dimension(150, 400));
           getContentPane().add(testListScroll);
           
               classPathText = new JTextArea();
               classPathText.setBorder(new TitledBorder("Classpath"));
               classPathText.setPreferredSize(new java.awt.Dimension(150,50));
               classPathText.setAutoscrolls(true);
               classPathText.setWrapStyleWord(true);
               classPathText.setText(TestExecuter.getClasspath());
           getContentPane().add(classPathText);
           
           	workingDirText.setBorder(new TitledBorder("Working directory where \"javac\" and \"java\" shall be executed"));
           	
           getContentPane().add(workingDirText);
           
           JButton testButton = new JButton("Run Test");
           testButton.addActionListener(new ActionListener() {
               public void actionPerformed(ActionEvent e) {
                   if(testList.getSelectedValue() == null){
                       JOptionPane.showMessageDialog(
                           null, "You must select a test first!",
                           "No Test Selected", 
                           JOptionPane.ERROR_MESSAGE);
                   }else{
                       String classpath = classPathText.getText();
                       	   //some cleanup
                           classpath = classpath.replaceAll(" ", "");
                           classpath = classpath.replaceAll("\n", "");
                       TestExecuter.setClasspath(classpath);
                       
                       TestAndModel tam = (TestAndModel) testList.getSelectedValue();
                       boolean compileOnlyGeneratedFiles = compileChoice.getSelectedItem()==COMPILE_ONLY_TEST;
                       try{
                           TestExecuter.compileAndRunTest(tam.test, workingDirText.getText(),compileOnlyGeneratedFiles,true);
                       }catch(Exception exc){
                           new ExceptionDialog(parent, exc);    
                       }
                   }
               }
           });
           
           getContentPane().add(compileChoice);
           getContentPane().add(testButton);
    }
    
    public static void addTest(String test, String model, String workingDir){
	DefaultListModel m = (DefaultListModel) testList.getModel();
	m.addElement(new TestAndModel(test,model,workingDir));
	if(testList.isVisible()){
	    testList.updateUI();
	}
    }
    
    public static class TestAndModel{
        public String test;
        public String model;
        public String workingDir;
        
        public TestAndModel(String test, String model, String workingDir){
            this.test = test;
            this.model = model;
            this.workingDir = workingDir;
        }
        
        public String toString(){
            return test;
        }
    }
}
