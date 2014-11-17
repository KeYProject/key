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
import javax.swing.tree.TreeSelectionModel;


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

    private static final String PROOF_FILE_NAME = "project.proof";

    /**
     * This class is a singleton class and this its only instance.
     */
    private static ExampleChooser instance;

    private final JTree exampleList;
    private final JButton loadButton;
    private final JButton loadProofButton;
    private final JButton cancelButton;
    private JTabbedPane tabPane;

    /**
     * The result value of the dialog. <code>null</code> if nothing to be loaded
     */
    private File fileToLoad = null;

    /**
     * The currently selected example. <code>null</code> if none selected
     */
    private Example selectedExample;

    /**
     * This class wraps a {@link File} and has a special {@link #toString()} method
     * only using the short file name w/o path.
     *
     * Used for displaying files in the examples list w/o prefix
     */
    public static class Example {
        /**
         * The default category under which examples range if they do not
         * have {@link #KEY_PATH} set.
         */
        private static final String DEFAULT_CATEGORY_PATH = "Unsorted";

        /**
         * The {@link Properties} key to specify the path in the tree.
         */
        private static final String KEY_PATH = "example.path";

        /**
         * The {@link Properties} key to specify the name of the example.
         * Directory name if left open.
         */
        private static final String KEY_NAME = "example.name";

        /**
         * The {@link Properties} key to specify the file for the example.
         * KEY_FILE_NAME by default
         */
        private static final String KEY_FILE = "example.file";

        /**
         * The {@link Properties} key to specify the proof file in the tree.
         * May be left open
         */
        private static final String KEY_PROOF_FILE = "example.proofFile";

        /**
         * The {@link Properties} key to specify the path in the tree.
         * Prefix to specify additional files to load. Append 1, 2, 3, ...
         */
        private static final String ADDITIONAL_FILE_PREFIX = "example.additionalFile.";

        /**
         * The {@link Properties} key to specify the path in the tree.
         * Prefix to specify export files which are not shown as tabs in the example wizard but are extracted to Java projects in the Eclipse integration.
         * Append 1, 2, 3, ...
         */
        private static final String EXPORT_FILE_PREFIX = "example.exportFile.";

        private final File exampleFile;
        private final File directory;
        private final String description;
        private final Properties properties;

        public Example(File file) throws IOException {
            this.exampleFile = file;
            this.directory = file.getParentFile();
            this.properties = new Properties();
            StringBuilder sb = new StringBuilder();
            extractDescription(file, sb, properties);
            this.description = sb.toString();
        }

        public File getDirectory() {
           return directory;
        }

        public File getProofFile() {
           return new File(directory, properties.getProperty(KEY_PROOF_FILE, PROOF_FILE_NAME));
        }

        public File getObligationFile() {
            return new File(directory, properties.getProperty(KEY_FILE, KEY_FILE_NAME));
        }

        public String getName() {
            return properties.getProperty(KEY_NAME, directory.getName());
        }

        public String getDescription() {
            return description;
        }

        public File getExampleFile() {
            return exampleFile;
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

        public List<File> getExportFiles() {
            ArrayList<File> result = new ArrayList<File>();
            int i = 1;
            while(properties.containsKey(EXPORT_FILE_PREFIX + i)) {
                result.add(new File(directory, properties.getProperty(EXPORT_FILE_PREFIX + i)));
                i++;
            }
            return result;
        }

        public String[] getPath() {
            return properties.getProperty(KEY_PATH, DEFAULT_CATEGORY_PATH).split("/");
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
            return properties.containsKey(KEY_PROOF_FILE);
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
	exampleList.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
	exampleList.setRootVisible(false);
	exampleList.addTreeSelectionListener(
	        new TreeSelectionListener() {
	            @Override
	            public void valueChanged(TreeSelectionEvent e) {
	                updateDescription();
	            }
		});
	exampleList.addMouseListener(new MouseAdapter() {
        @Override
	    public void mouseClicked(MouseEvent e){
		if(e.getClickCount() == 2){
		    loadButton.doClick();
		}
	    }
	});
	final JScrollPane exampleScrollPane = new JScrollPane(exampleList);
	exampleScrollPane.setBorder(new TitledBorder("Examples"));

	//create description label
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
        @Override
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
            @Override
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
        @Override
	    public void actionPerformed(ActionEvent e) {
	        fileToLoad = null;
		setVisible(false);
	    }
	});
	buttonPanel.add(cancelButton);
        ActionListener escapeListener = new ActionListener() {
            @Override
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

        // select first example
        DefaultMutableTreeNode firstLeaf = ((DefaultMutableTreeNode)model.getRoot()).getFirstLeaf();
        TreePath pathToFirstLeaf = new TreePath(firstLeaf.getPath());
        exampleList.getSelectionModel().setSelectionPath(pathToFirstLeaf);
        exampleList.makeVisible(pathToFirstLeaf);

	// show
        getContentPane().setLayout(new BoxLayout(getContentPane(),
                                                 BoxLayout.Y_AXIS));
	setSize(800,400);
	setLocationRelativeTo(MainWindow.getInstance());
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
            return "<Error reading file: " + f + ">";
        }
    }

    private static StringBuilder extractDescription(File file, StringBuilder sb, Properties properties)
            throws IOException {
        BufferedReader r = null;
        try {
            r = new BufferedReader(new FileReader(file));
            String line;
            boolean emptyLineSeen = false;
            while((line = r.readLine()) != null) {
                if(emptyLineSeen) {
                    sb.append(line).append("\n");
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
        return sb;
    }



    private void updateDescription() {

        TreePath selectionPath = exampleList.getSelectionModel().getSelectionPath();
        if(selectionPath == null) {
            return;
        }

        DefaultMutableTreeNode node =
                (DefaultMutableTreeNode) selectionPath.getLastPathComponent();
        Object nodeObj = node.getUserObject();
        tabPane.removeAll();

        if (nodeObj instanceof Example) {
            Example example = (Example) nodeObj;

            if(example != selectedExample) {
                addTab(example.getDescription().toString(), "Description", true);
                final String fileAsString = fileAsString(example.getObligationFile());
                final int p = fileAsString.lastIndexOf("\\problem");
                if (p >= 0) {
                    addTab(fileAsString.substring(p), "Proof Obligation", false);
                }
                for (File file : example.getAdditionalFiles()) {
                    addTab(fileAsString(file), file.getName(), false);
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

    private void addTab(String string, String name, boolean wrap) {
        JTextArea area = new JTextArea();
        area.setText(string);
        area.setFont(new Font(Font.MONOSPACED, Font.PLAIN, area.getFont().getSize()));
        area.setCaretPosition(0);
        area.setEditable(false);
        area.setWrapStyleWord(true);
        area.setLineWrap(wrap);
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
}