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
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.JTree;
import javax.swing.KeyStroke;
import javax.swing.border.TitledBorder;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;


public final class ExampleChooser extends JDialog {
    /**
     * This path is also accessed by the Eclipse integration of KeY
     * to find the right examples.
     */
    public static final String EXAMPLES_PATH = "examples";

    private static final long serialVersionUID = -4405666868752394532L;

    /**
     * This constant is accessed by the eclipse based projects.
     */
    public static final String KEY_FILE_NAME = "project.key";

    private static final String README_NAME = "README.txt";

    private static ExampleChooser instance;

    private final JTree exampleList;
    private final JButton loadButton;
    private final JButton loadProofButton;
    private final JButton cancelButton;
    private JTabbedPane tabPane;

    private File fileToLoad = null;

    private Example selectedExample;

    /**
     * This class wraps a {@link File} and has a special {@link #toString()} method
     * only using the short file name w/o path.
     *
     * Used for displaying files in the examples list w/o prefix
     */
    public static class Example {
        private static final String ADDITIONAL_FILE_PREFIX = "example.additionalFile.";
        private File directory;
        private StringBuilder description;
        private Properties properties;

        public Example(File file) throws IOException {
            this.directory = file.getParentFile();
            this.properties = new Properties();
            this.description = new StringBuilder();

            BufferedReader r = null;
            try {
                r = new BufferedReader(new FileReader(file));
                String line;
                boolean emptyLineSeen = false;
                while((line = r.readLine()) != null) {
                    if(emptyLineSeen) {
                        description.append(line).append("\n");
                    } else {
                        String trimmed = line.trim();
                        if(trimmed.length() == 0) {
                            emptyLineSeen = true;
                        } else if(trimmed.startsWith("#")) {
                            // ignore
                        } else {
                            String[] entry = trimmed.split(" *[:=] *", 2);
                            if(entry.length > 1) {
                                properties.put(entry[0], entry[1]);
                            }
                        }
                    }
                }
            } finally {
                if(r != null) {
                    try { r.close(); }
                    catch(IOException ex) { };
                }
            }
        }

        public File getProofFile() {
           return new File(directory, properties.getProperty("example.proofFile", "project.proof"));
        }

        public File getObligationFile() {
            return new File(directory, properties.getProperty("example.file", "project.key"));
        }

        public String getName() {
            return properties.getProperty("example.name", directory.getName());
        }

        public CharSequence getDescription() {
            return description;
        }

        public List<File> getAdditionalFiles() {
            ArrayList<File> result = new ArrayList<File>();
            int i = 1;
            while(properties.containsKey(ADDITIONAL_FILE_PREFIX + i)) {
                result.add(new File(directory, properties.getProperty(ADDITIONAL_FILE_PREFIX + i)));
                i++;
            }
            return result;
        }

        public String[] getPath() {
            return properties.getProperty("example.path", "").split("/");
        }

        @Override
        public String toString() {
            return getName();
        }

        public void addToTreeModel(DefaultTreeModel model) {
            DefaultMutableTreeNode node =
                    findChild((DefaultMutableTreeNode) model.getRoot(), getPath(), 0);
            node.add(new DefaultMutableTreeNode(this));
        }

        private DefaultMutableTreeNode findChild(DefaultMutableTreeNode root, String[] path, int from) {
            if(from == path.length) {
                return root;
            }
            Enumeration<?> en = root.children();
            while(en.hasMoreElements()) {
                DefaultMutableTreeNode node = (DefaultMutableTreeNode) en.nextElement();
                if(node.getUserObject().equals(path[from])) {
                    return findChild(node, path, from + 1);
                }
            }
            // not found ==> add new
            DefaultMutableTreeNode node = new DefaultMutableTreeNode(path[from]);
            root.add(node);
            return findChild(node, path, from + 1);
        }

        public boolean hasProof() {
            return properties.containsKey("example.proofFile");
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
	final DefaultTreeModel model = new DefaultTreeModel(new DefaultMutableTreeNode());
	List<Example> examples = listExamples(examplesDir);
	for (Example example : examples) {
	   example.addToTreeModel(model);
	}

	exampleList = new JTree();
	exampleList.setModel(model);
	exampleList.setRootVisible(false);
	exampleList.addTreeSelectionListener(
	        new TreeSelectionListener() {
	            @Override
	            public void valueChanged(TreeSelectionEvent e) {
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

	//create description label
//	descriptionText = new JTextArea();
//	descriptionText.setEditable(false);
//	descriptionText.setLineWrap(true);
//	descriptionText.setWrapStyleWord(true);
//	final JScrollPane descriptionScrollPane
//		= new JScrollPane(descriptionText);
	tabPane = new JTabbedPane(JTabbedPane.TOP);

	JSplitPane split = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
	split.add(exampleScrollPane);
	split.add(tabPane);
	split.setDividerLocation(300);
	listPanel.add(split, BorderLayout.CENTER);

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
	loadButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
	        assert selectedExample != null;
		fileToLoad = selectedExample.getObligationFile();
		setVisible(false);
	    }
	});
	buttonPanel.add(loadButton);
	getRootPane().setDefaultButton(loadButton);

	//create "load proof" button
        loadProofButton = new JButton("Load Proof");
        loadProofButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                assert selectedExample != null;
                assert selectedExample.hasProof();
                fileToLoad = selectedExample.getProofFile();
                setVisible(false);
            }
        });
        buttonPanel.add(loadProofButton);

	//create "cancel" button
	cancelButton = new JButton("Cancel");
	cancelButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
	        fileToLoad = null;
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
        DefaultMutableTreeNode firstLeaf = ((DefaultMutableTreeNode)model.getRoot()).getFirstLeaf();
        exampleList.getSelectionModel().setSelectionPath(new TreePath(firstLeaf));

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
    public static List<Example> listExamples(File examplesDir) {
        List<Example> result = new LinkedList<Example>();

        String line;
        BufferedReader br = null;
        try {
            br = new BufferedReader(
                    new FileReader(new File(new File(examplesDir, "index"), "samplesIndex.txt")));
            while((line = br.readLine()) != null) {
                line = line.trim();
                if(line.startsWith("#") || line.length() == 0) {
                    continue;
                }
                File f = new File(examplesDir, line);
                try {
                    result.add(new Example(f));
                } catch (IOException e) {
                    System.err.println("Cannot parse example " +  f + "; ignoring it.");
                    e.printStackTrace();
                }
            }
        } catch (IOException e) {
            System.err.println("Error while reading samples");
            e.printStackTrace();
        } finally {
            try {
                if(br != null) {
                    br.close();
                }
            } catch (IOException e) {
                System.err.println("Error while reading samples");
                e.printStackTrace();
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

    private static String fileAsString(File f) {
        try {
            byte[] buffer = new byte[(int) f.length()];
            FileInputStream fis = new FileInputStream(f);
            fis.read(buffer);
            fis.close();
            return new String(buffer);
        } catch (IOException e) {
            e.printStackTrace();
            return "<Error reading file: " + f + ">";
        }
    }

    private void updateDescription() {

        DefaultMutableTreeNode node =
                (DefaultMutableTreeNode) exampleList.getSelectionModel().getSelectionPath().getLastPathComponent();
        Object nodeObj = node.getUserObject();
        tabPane.removeAll();

        if (nodeObj instanceof Example) {
            Example example = (Example) nodeObj;

            if(example != selectedExample) {
                addTab(example.getDescription().toString(), "Description");
                addTab(fileAsString(example.getObligationFile()), "Proof Obligation");
                for (File file : example.getAdditionalFiles()) {
                    addTab(fileAsString(file), file.getName());
                }
                loadButton.setEnabled(true);
                loadProofButton.setEnabled(example.hasProof());
                selectedExample = example;
            }
        } else {
            selectedExample = null;
            loadButton.setEnabled(false);
            loadProofButton.setEnabled(false);
        }
    }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    private void addTab(String string, String name) {
        // TODO Auto-generated method stub
        JTextArea area = new JTextArea();
        area.setText(string);
        area.setFont(new Font(Font.MONOSPACED, Font.PLAIN, area.getFont().getSize()));
        area.setCaretPosition(0);
        area.setEditable(false);
        tabPane.add(new JScrollPane(area), name);
    }

    /**
     * Shows the dialog, using the passed examples directory. If null is passed,
     * tries to find examples directory on its own.
     */
    public static File showInstance(String examplesDirString) {
        // get examples directory
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
	final File result = instance.fileToLoad;
	return result;
    }
}