// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.configuration;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.HashMap;

import javax.swing.*;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.DefaultTableCellRenderer;

import de.uka.ilkd.key.gui.KeYMediator;

public class LibrariesConfiguration extends JDialog {
    
    private LibrariesSettings settingsFromFile;
    private KeYMediator mediator = null;
    private JButton remove, add, ok, cancel;
    
    private LibrariesTableModel tableModel;
    private HashMap<String,Boolean> libToSel;
    private JTable table;
    
    /** creates a new Libraries selection dialog 
     */
    public LibrariesConfiguration (KeYMediator mediator, LibrariesSettings settings) {  
	super(new JFrame(), "Libraries", true);
        settingsFromFile = settings;
        libToSel= settingsFromFile.getLibraries();
        
        // converts the HashMap to the arrays libraries and selected
        int size = libToSel.keySet().size();
        String[] l = new String[size];
        boolean[] s = new boolean[size];

        int i=0;
        for (final String lib : libToSel.keySet()) {
            l[i] = lib;
            i++;
        }
  
        // sorts the libraries array
        java.util.Arrays.sort(l,0,size);

        for(int j=0;j<size;j++){
            s[j]= ((Boolean)libToSel.get(l[j])).booleanValue();
        }
        
        setMediator(mediator);
	initizializeDialog(l,s);
	setLocation(70,70);
	setSize(360,200);
        setVisible(false);
    }

    /** sets the mediator to correspond with other gui elements
     * @param mediator the KeYMediator
     */
    public void setMediator(KeYMediator mediator) {	
	this.mediator = mediator;
    }

    private void pushSettings(String[] libraries,boolean[] selected) {
        HashMap<String, Boolean> hm = new HashMap<String, Boolean>();
        for(int i=0;i<libraries.length;i++){
            hm.put(libraries[i],new Boolean(selected[i]));
        }
        settingsFromFile.setLibraries(hm);
    }


    /** initializes the library configuration dialog */

    public void initizializeDialog(String[] libraries,boolean[] selected) {	
        JPanel buttonPanel = new JPanel(new GridLayout(1,4));
	ok = new JButton("OK");
	
        ok.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent ae) {
            
                    if(tableModel.settingsChanged())
                    {
                        int res = JOptionPane.showOptionDialog
                            (LibrariesConfiguration.this,
                             "Your changes will become effective when "+
                             "the next problem is loaded.\n", 
                             "Libraries Settings", 
                             JOptionPane.DEFAULT_OPTION,
                             JOptionPane.QUESTION_MESSAGE, null,
                             new Object[]{"OK", "Cancel"}, "OK");
                        if (res==0){
                            pushSettings(tableModel.getLibraries(),tableModel.getSelected());
                        }
                    }
		    dispose();
		}
	    });
	cancel = new JButton("Cancel");
	cancel.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent ae) {
		    dispose();
		}
	    });
	ok.setSize(new Dimension(50,25));
        cancel.setSize(new Dimension(100,50));
        
        add = new JButton("Add");
        add.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent ae) {

                JFileChooser fileChooser = new JFileChooser(new File("."));
                fileChooser
                        .setFileSelectionMode(JFileChooser.FILES_ONLY);
                fileChooser
                        .setFileFilter(new javax.swing.filechooser.FileFilter() {
                            public boolean accept(File f) {
                                return f.isDirectory()|| f.toString().endsWith(".key");
                            }

                            public String getDescription() {
                                return "KeY files";
                            }
                        });
                fileChooser.setDialogTitle ("Select a KeY library");
                int result = fileChooser.showOpenDialog(LibrariesConfiguration.this);
                if (result==JFileChooser.APPROVE_OPTION){
                    File file = fileChooser.getSelectedFile();
                    tableModel.addLibrary(file.toString(),false);
                }
            }
        });
        
        remove = new JButton("Remove");
        remove.setEnabled(false);
        remove.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent ae) {
                int row = table.getSelectedRow();
                String file = (String) tableModel.getValueAt(row, 0);
                String fileName = file;
                if (file.startsWith(File.separator)) {
                    int i = file.lastIndexOf(File.separator);
                    if (i > -1)
                        fileName = file.substring(i + 1, file.length());
                }

                int res = JOptionPane.showOptionDialog(
                        LibrariesConfiguration.this, "Delete Library "
                                + fileName + "?", "Delete Library",
                        JOptionPane.DEFAULT_OPTION,
                        JOptionPane.QUESTION_MESSAGE, null, new Object[] {
                                "OK", "Cancel" }, "OK");
                if (res == 0) {
                    tableModel.removeLibrary(row);
                }

            }
        });
        
        buttonPanel.add(ok);
	buttonPanel.add(cancel);
	buttonPanel.add(add);
        buttonPanel.add(remove);
        buttonPanel.setSize(350,100);
        
        tableModel = new LibrariesTableModel(libraries,selected);
        table = new JTable(tableModel);
        table.setDefaultRenderer(Object.class,new LibCellRenderer());
        table.setPreferredScrollableViewportSize(new Dimension(340, 110));
        table.setSize(300,100);
      
        //Create the scroll pane and add the table to it.
        JScrollPane scrollPane = new JScrollPane(table);
        //tablePanel.add(scrollPane);
        
        DefaultListSelectionModel lsModel = new DefaultListSelectionModel();
        lsModel.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
      
        lsModel.addListSelectionListener(new ListSelectionListener(){
           public void valueChanged(ListSelectionEvent e){
               int row =table.getSelectedRow();
               if (row ==-1){
                   remove.setEnabled(false);
                   return;
               }
               if (!tableModel.getLibraries()[row].
                     startsWith(File.separator)){
                   remove.setEnabled(false);
               } else{
                   remove.setEnabled(true);
               }
           }
        });
    
        table.setEditingColumn(1);
        table.setSelectionModel(lsModel);
        table.getColumnModel().getColumn(0).setPreferredWidth(250);
        table.getColumnModel().getColumn(1).setPreferredWidth(50);
    
	getContentPane().setLayout(new FlowLayout());
	getContentPane().add(scrollPane);
	getContentPane().add(buttonPanel);	
	
    }

    class LibrariesTableModel extends AbstractTableModel {
        private String[] columnNames = {"Library Name","Active"};
        
         String libraries[];
         boolean sel[];
         boolean changed = false;
    

        public LibrariesTableModel(String[] libs,boolean[] sel){
            this.libraries =libs;
            this.sel=sel;
        }
        
        public int getColumnCount() {
            return 2;
        }

        public int getRowCount() {
            return libraries.length;
        }

        public String getColumnName(int col) {
            return columnNames[col];
        }

        public Object getValueAt(int row, int col) {
            if (col==0)
                return this.libraries[row];
            else {
                return new Boolean(sel[row]);
            }
        }

     
        public Class<? extends Object> getColumnClass(int c) {
            return getValueAt(0, c).getClass();
        }

        
        public boolean isCellEditable(int row, int col) {
            if (col < 1) {
                return false;
            } else {
                return true;
            }
        }

        
        public void setValueAt(Object value, int row, int col) {
            if (col==0)
                libraries[row]=((String)value);
            else sel[row]=  ((Boolean)value).booleanValue();
            fireTableCellUpdated(row, col);
            changed=true;
        }
        
        public String[] getLibraries(){
            return libraries;
        }
        
        public boolean[] getSelected(){
            return sel;
        }
        
        public void addLibrary(String file, boolean selected){
            String[] newLib = new String[libraries.length+1];
            boolean[] newSel = new boolean[libraries.length+1];
            for (int i=0;i<libraries.length;i++){
                newLib[i]=libraries[i];
                newSel[i]= sel[i];
            }
            newLib[newLib.length-1]=file;
            newSel[newLib.length-1]=selected;

            libraries = newLib;
            sel = newSel;
            this.fireTableRowsInserted(libraries.length-1,libraries.length-1);
            changed = true;
        }

        public void removeLibrary(int a){
            String[] newLib = new String[libraries.length-1];
            boolean[] newSel = new boolean[libraries.length-1];
            for (int i=0;i<a;i++){
                newLib[i]=libraries[i];
                newSel[i]= sel[i];
            }
            if (a<libraries.length-1)
            for (int i=a;i<libraries.length-1;i++){
                newLib[i]=libraries[i+1];
                newSel[i]= sel[i+1];
            }
            libraries = newLib;
            this.fireTableRowsDeleted(libraries.length-1,libraries.length-1);
            changed = true;
        }

        public boolean settingsChanged(){
            return changed;
        }
        
    }
    
   
    
    public class LibCellRenderer extends DefaultTableCellRenderer {
        
        public String getFileName(String path){
            if (!path.startsWith(File.separator))
                return path;
            int i= path.lastIndexOf(File.separator);
            if (i>-1)
                return path.substring(i+1,path.length());
            return path;
        }
        
        public Component getTableCellRendererComponent(
                JTable table, Object col,
                boolean isSelected, boolean hasFocus,
                int row, int column) {
                Color grey = new Color(200,200,200);
                Color white = new Color(255,255,255);
                if (col instanceof Boolean){
                    return super.getTableCellRendererComponent(table,
                            col,isSelected,hasFocus,row,column);
                } else if (col instanceof String){
                    String file = (String)col;
                    if (file.startsWith(File.separator))
                        setBackground(white);
                    else setBackground(grey);

                    return super.getTableCellRendererComponent(table,
                            getFileName(file),isSelected,hasFocus,row,column);
                } else
                return super.getTableCellRendererComponent(table,col,isSelected,hasFocus,row,column);
            }    
        }
}
