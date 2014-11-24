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

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.util.List;
import java.util.Map;

import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.MainWindow;

public class SystemInfoAction extends MainWindowAction {

    private static final long serialVersionUID = -4197309658998177157L;
    private static final int TEXT_ROWS = 20;
    private static final int TEXT_COLS = 60;

    public SystemInfoAction(MainWindow mainWindow) {
        super(mainWindow);
	    setName("System Info");
//        setIcon(IconFactory.help(16));
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Object[] contents = new Object[6];
        contents[0] = "KeY info:\n";
        String params = System.getProperty("sun.java.command");
        if (params == null) params = "(unknown)";
        int i = params.indexOf("Main");
        if (i > 0) params = params.substring(i+4);
        java.lang.management.RuntimeMXBean rmb = java.lang.management.ManagementFactory.getRuntimeMXBean();
        final String keyInfoText = "Version: "+Main.VERSION
                        + "\nKeY parameters: "+ params
                        + "\nVM parameters: "+formatList(rmb.getInputArguments());
        JTextArea keyInfo = new JTextArea(keyInfoText,3,TEXT_COLS);
        keyInfo.setEditable(false);
        contents[1] = keyInfo;
        
        contents[2] = getMemoryInfo()
                        +"\n\nEnvironment variables:\n";
        JScrollPane scroll = new JScrollPane();
        JTextArea text = new JTextArea(getEnv(),TEXT_ROWS/3,40);
        text.setEditable(false);
        text.setCaretPosition(0);
        scroll.setViewportView(text);
        contents[3] = scroll;
        
        contents[4] = "\nJava properties:\n";
        JScrollPane scroll2 = new JScrollPane();
        JTextArea text2 = new JTextArea(getProperties(),TEXT_ROWS,40);
        text2.setEditable(false);
        text2.setCaretPosition(0);
        scroll2.setViewportView(text2);
        contents[5] = scroll2;
        
		JOptionPane pane = new JOptionPane(
	                contents, JOptionPane.INFORMATION_MESSAGE,
	        JOptionPane.DEFAULT_OPTION);
		JDialog dialog = pane.createDialog(mainWindow, "System information");
	    dialog.setVisible(true);
    }
    
    @SuppressWarnings("finally")
    private String getProperties() {
        StringBuffer sb = new StringBuffer();
        java.util.Properties props;
        try {
            props = System.getProperties();
            formatMap(sb, props);
        } finally {
            return sb.toString();
        }
    }
    

    @SuppressWarnings("finally")
    private String getEnv() {
        StringBuffer sb = new StringBuffer();
        try {
            formatMap(sb, System.getenv());
        } finally {
            return sb.toString();
        }
    }

    private void formatMap(StringBuffer sb, Map<?,?> props) {
        for (Object o: props.keySet()) {
            sb.append(o);
            sb.append("=\"");
            sb.append(props.get(o));
            sb.append("\"\n");
        }
    }
    
    private String formatList (List<?> l) {
        StringBuffer sb = new StringBuffer();
        for (Object o: l) {
            sb.append(o);
            sb.append(" ");
        }
        sb.deleteCharAt(sb.length()-1);
        return sb.toString();
    }

    private String getMemoryInfo() {
        Runtime rt = Runtime.getRuntime();
        rt.gc(); // call garbage collection to normalize stats

        StringBuilder sb = new StringBuilder();
        long maxMemory = rt.maxMemory();
        long allocatedMemory = rt.totalMemory();
        long freeMemory = rt.freeMemory();

        sb.append("\nAvailable processors: " + rt.availableProcessors());
        sb.append("\nFree VM memory: " + (freeMemory / 1024 / 1024) +" MB");
        sb.append("\nAllocated VM memory: " + (allocatedMemory / 1024 / 1024) +" MB");
        sb.append("\nMax VM memory: " + (maxMemory / 1024 / 1024) +" MB");
        sb.append("\nTotal free VM memory: " + ((freeMemory + (maxMemory - allocatedMemory)) / 1024 / 1024) +" MB");
        return sb.toString();
    }
}