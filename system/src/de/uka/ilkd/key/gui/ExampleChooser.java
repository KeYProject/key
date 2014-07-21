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

package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

import javax.swing.BoxLayout;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.KeyStroke;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;


public final class ExampleChooser extends JDialog {
    /**
     * This path is also accessed by the Eclipse integration of KeY
     * to find the right examples.
     */
    public static final String EXAMPLES_PATH =  
		    "examples" + File.separator + "firstTouch";
    private static final long serialVersionUID = -4405666868752394532L;
    /**
     * This constant is accessed by the eclipse based projects.
     */
    public static final String KEY_FILE_NAME = "project.key";
    private static final String README_NAME = "README.txt";
    
    private static ExampleChooser instance;
    
    private final JList exampleList;
    private final JTextArea descriptionText;    
    private final JButton loadButton;
    private final JButton cancelButton;
    
    private boolean success = false;
    
    /**
     * This class wraps a {@link File} and has a special {@link #toString()} method
     * only using the short file name w/o path.
     * 
     * Used for displaying files in the examples list w/o prefix
     */
    public static class ShortFile {
        private File file;

        public ShortFile(File file) {
            this.file = file;
        }
        
        public File getFile() {
           return file;
        }

        @Override 
        public String toString() {
            return file.getName().substring(3); // remove leading index number
        }
    }
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    private ExampleChooser(File examplesDir) {
	super(MainWindow.getInstance(), "Load Example", true);
	assert examplesDir != null;
	assert examplesDir.isDirectory();
	
	//create list panel
	final JPanel listPanel = new JPanel();
	listPanel.setLayout(new BorderLayout());
	getContentPane().add(listPanel);
	
	//create example list
	final DefaultListModel model = new DefaultListModel();
	List<ShortFile> examples = listExamples(examplesDir);
	for (ShortFile example : examples) {
	   model.addElement(example);
	}
	exampleList = new JList();
	exampleList.setModel(model);
	exampleList.addListSelectionListener(
		new ListSelectionListener() {
		    public void valueChanged(ListSelectionEvent e) {
			updateDescription();
		    }
		});	
	exampleList.addMouseListener(new MouseAdapter() {
	    public void mouseClicked(MouseEvent e){
		if(e.getClickCount() == 2){
		    loadButton.doClick();
		}
	    }
	});	
	final JScrollPane exampleScrollPane = new JScrollPane(exampleList);
	exampleScrollPane.setBorder(new TitledBorder("Examples"));
	listPanel.add(exampleScrollPane, BorderLayout.WEST);
	
	//create description label
	descriptionText = new JTextArea();
	descriptionText.setEditable(false);
	descriptionText.setLineWrap(true);
	descriptionText.setWrapStyleWord(true);
	final JScrollPane descriptionScrollPane 
		= new JScrollPane(descriptionText);
	descriptionScrollPane.setBorder(new TitledBorder("Description"));
	listPanel.add(descriptionScrollPane, BorderLayout.CENTER);
	
	//create button panel
	final JPanel buttonPanel = new JPanel();
	buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
	final Dimension buttonDim = new Dimension(140, 27);
        buttonPanel.setMaximumSize(new Dimension(Integer.MAX_VALUE, 
                                                 (int)buttonDim.getHeight() 
                                                     + 10));
	getContentPane().add(buttonPanel);	
	
	//create "load" button
	loadButton = new JButton("Load Example");
	loadButton.setPreferredSize(buttonDim);
	loadButton.setMinimumSize(buttonDim);
	loadButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) { 
		success = true;
		setVisible(false);
	    }
	});
	buttonPanel.add(loadButton);
	getRootPane().setDefaultButton(loadButton);

	//create "cancel" button
	cancelButton = new JButton("Cancel");
	cancelButton.setPreferredSize(buttonDim);
	cancelButton.setMinimumSize(buttonDim);
	cancelButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		success = false;
		setVisible(false);
	    }
	});
	buttonPanel.add(cancelButton);
        ActionListener escapeListener = new ActionListener() {
            public void actionPerformed(ActionEvent event) {
                if(event.getActionCommand().equals("ESC")) {
                    cancelButton.doClick();
                }
            }
        };
        cancelButton.registerKeyboardAction(
                            escapeListener,
                            "ESC",
                            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                            JComponent.WHEN_IN_FOCUSED_WINDOW);	

        //select first example, or disable load button
	if(model.size() == 0) {
	    loadButton.setEnabled(false);
	} else {
	    exampleList.setSelectedIndex(0);
	}
	
	//show
        getContentPane().setLayout(new BoxLayout(getContentPane(), 
                                                 BoxLayout.Y_AXIS));	
	setSize(800,400);
	setLocationRelativeTo(MainWindow.getInstance());
    }	
    
    /**
     * Lists all examples in the given directory. 
     * This method is also accessed by the eclipse based projects.
     * @param examplesDir The examples directory to list examples in.
     * @return The found examples.
     */
    public static List<ShortFile> listExamples(File examplesDir) {
       File[] examples = examplesDir.listFiles();
       Arrays.sort(examples, new Comparator<File>() {
          public int compare(File f1, File f2) {
             return f1.getName().compareToIgnoreCase(f2.getName());
          }
       });
       List<ShortFile> result = new LinkedList<ExampleChooser.ShortFile>();
       for (File example : examples) {
          if (example.isDirectory()) {
             final File keyfile = new File(example, KEY_FILE_NAME);
             if (keyfile.isFile()) {
                result.add(new ShortFile(example));
             }
          }
       }
       return result;
    }
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------    
    
    private static File lookForExamples() {
        
	// greatly simplified version without parent path lookup.
        return new File(System.getProperty("key.home"), EXAMPLES_PATH);
    }
    
    
    private void updateDescription() {
       ShortFile selectedExample = (ShortFile) exampleList.getSelectedValue();
       String description = readDescription(selectedExample);
       descriptionText.setText(description);
       descriptionText.getCaret().setDot(0);
    }
    
    public static String readDescription(ShortFile example) {
      final File readme = new File(example.file, README_NAME);
      if (readme.isFile()) {
         BufferedReader br = null;
         try {
            br = new BufferedReader(new FileReader(readme));
            final StringBuilder sb = new StringBuilder();
            final String ls = System.getProperty("line.separator");
            String line;
            while ((line = br.readLine()) != null) {
               sb.append(line);
               sb.append(ls);
            }
            return sb.toString();
         }
         catch (IOException e) {
            return "Reading description from README file failed.";
         }
         finally {
            try {
               if (br != null) {
                  br.close();
               }
            }
            catch (IOException e) {
               // Nothing to do.
            }
         }
      }
      else {
         return "No description available.";
      }
    }
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Shows the dialog, using the passed examples directory. If null is passed,
     * tries to find examples directory on its own.
     */
    public static File showInstance(String examplesDirString) {
	//get examples directory
	File examplesDir;
	if(examplesDirString == null) {
	    examplesDir = lookForExamples();
	} else {
        examplesDir = new File(examplesDirString);
    }
	
        if (examplesDir == null || !examplesDir.isDirectory()) {
            JOptionPane.showMessageDialog(MainWindow.getInstance(),
                    "The examples directory cannot be found.\n"+
                    "Please install them at " + 
                            (examplesDirString == null ? System.getProperty("key.home") +"/" : examplesDirString), 
                    "Error loading examples",
                    JOptionPane.ERROR_MESSAGE);
            return null;
        }

	//show dialog
	if(instance == null) {
	    instance = new ExampleChooser(examplesDir);
	}
	instance.setVisible(true);
	
	//return result
	final File result = instance.success 
        		    ? new File(((ShortFile)instance.exampleList
        			                     .getSelectedValue()).file, 
        			       KEY_FILE_NAME) 
        	            : null;	
	return result;
    }
}