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

package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.Component;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.AbstractCellEditor;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.ScrollPaneConstants;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
import javax.swing.event.TableModelEvent;
import javax.swing.plaf.basic.BasicProgressBarUI;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;
import javax.swing.table.TableColumn;
import javax.swing.table.TableColumnModel;

import de.uka.ilkd.key.gui.smt.ProgressModel.ProcessColumn.ProcessData;
import de.uka.ilkd.key.gui.smt.ProgressTable.ProgressTableListener;
import de.uka.ilkd.key.gui.utilities.ClickableMessageBox;
import de.uka.ilkd.key.gui.utilities.ClickableMessageBox.ClickableMessageBoxListener;




public class ProgressDialog extends JDialog{

        private static final long serialVersionUID = 1L;
        private final ProgressTable   table;
        private JButton  applyButton;
        private JButton  stopButton;
        private JScrollPane scrollPane;

        private JProgressBar progressBar;
        private ClickableMessageBox statusMessages;
        private final ProgressDialogListener listener;
        public enum Modus {stopModus,discardModus}

    private Modus modus = Modus.stopModus;
        private Box statusMessageBox;
        
        private boolean counterexample;
       
        
        public static interface ProgressDialogListener extends ProgressTableListener{
                public void applyButtonClicked();
                public void stopButtonClicked();
                public void discardButtonClicked();
                public void additionalInformationChosen(Object obj);
              
        }
     
     
        
  
        
        public ProgressDialog(ProgressModel model,ProgressDialogListener listener, boolean counterexample,
                        int resolution, int progressBarMax,String[] labelTitles,String ... titles) {
                this.counterexample = counterexample;
        	    table = new ProgressTable(resolution,listener,labelTitles); 
                table.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
                table.setModel(model,titles);
                this.listener = listener;
                this.setLocationByPlatform(true);
                if(counterexample){
                	this.setTitle("SMT Counterexample Search");
                }
                else{
                	this.setTitle("SMT Interface");
                }
                
                getProgressBar().setMaximum(progressBarMax);
             
                setDefaultCloseOperation(DISPOSE_ON_CLOSE);
                setModal(true);
                Container contentPane = this.getContentPane();
                contentPane.setLayout(new GridBagLayout());
                Box buttonBox = Box.createHorizontalBox();
                buttonBox.add(Box.createHorizontalGlue());
                buttonBox.add(getStopButton());
                buttonBox.add(Box.createHorizontalStrut(5));
                if(!counterexample){
                	buttonBox.add(getApplyButton());
                    buttonBox.add(Box.createHorizontalStrut(5));
                }
                
                
                GridBagConstraints constraints = new GridBagConstraints(0, 0, 1, 1, 1.0, 0.0, 
                        GridBagConstraints.CENTER, 
                        GridBagConstraints.BOTH, 
                        new Insets(5,5,0,5), 0,0);
                
                contentPane.add(getProgressBar(), constraints);
                constraints.gridy ++;
                constraints.weighty = 2.0;
                contentPane.add(getScrollPane(), constraints);
                constraints.gridy ++;
                constraints.weighty = 1.0;
                contentPane.add(getStatusMessageBox(), constraints);
                constraints.gridy ++;
                constraints.weighty = 0.0;
                constraints.insets.bottom = 5;
                contentPane.add(buttonBox, constraints);
                this.pack();
        }
        
        

        
        public void addInformation(String title,Color color, Object information){
        	
        		getStatusMessages().add(information, title, color);
        		if(!getStatusMessageBox().isVisible()){
        			getStatusMessageBox().setVisible(true);        
        			this.pack();
        		}
        }
        
        
        

        
        public void setProgress(int value){
                getProgressBar().setValue(value);
        }
        
        public JProgressBar getProgressBar(){
                if(progressBar == null){
                        progressBar = new JProgressBar();
                  
                }
                
                return progressBar;
        }
        
        public ClickableMessageBox getStatusMessages() {

        	if(statusMessages == null){
        		statusMessages = new ClickableMessageBox();
           		statusMessages.add(new ClickableMessageBoxListener() {
					
					@Override
					public void eventMessageClicked(Object object) {
						  listener.additionalInformationChosen(object);
						
					}
				});
          	}        
        	return statusMessages;
		}
     
        public Box getStatusMessageBox() {
        	if(statusMessageBox == null){
        		statusMessageBox = Box.createVerticalBox();
        		JScrollPane pane = new JScrollPane(getStatusMessages());
        		Dimension dim = pane.getPreferredSize();
        		dim.height = 80;
        		pane.setPreferredSize(dim);
        		statusMessageBox.add(pane);
        		statusMessageBox.add(new JLabel("For more information please click on the particular message."));
        		statusMessageBox.setVisible(false);
        	}
        	
        	return statusMessageBox;
		}
        

        
   
        
        
        private JButton getApplyButton() {
                if(applyButton == null){
                       applyButton = new JButton("Apply");
                       applyButton.setEnabled(false);
                       applyButton.addActionListener(new ActionListener() {
                        
                        @Override
                        public void actionPerformed(ActionEvent e) {
                                listener.applyButtonClicked();
                        }
                });
                       
                }
                return applyButton;
        }
        
        private JScrollPane getScrollPane() {
                if(scrollPane == null){
                        scrollPane = new JScrollPane(table,ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
                                        ScrollPaneConstants.HORIZONTAL_SCROLLBAR_ALWAYS
                                        );
                        
                        Dimension dim = new Dimension(table.getPreferredSize());
                        dim.width += (Integer)UIManager.get("ScrollBar.width")+2;
                        dim.height = scrollPane.getPreferredSize().height;
                        scrollPane.setPreferredSize(dim);
                        
                }
                return scrollPane;
        }
        
        private JButton getStopButton() {
                if(stopButton == null){
                        stopButton = new JButton("Stop");
                        stopButton.addActionListener(new ActionListener() {
                                
                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        if(modus.equals(Modus.discardModus)){
                                                listener.discardButtonClicked();
                                        }
                                        if(modus.equals(Modus.stopModus))
                                        {
                                                listener.stopButtonClicked();        
                                        }
                                        
                                }
                        });
                 }
                return stopButton;
        }
        
        public void setModus(Modus m){
                modus = m;
                switch(modus){
                case discardModus:
                        stopButton.setText("Discard");
                        if(applyButton!=null)
                        applyButton.setEnabled(true);
                        break;
                case stopModus:
                        stopButton.setText("Stop");
                        if(applyButton!=null)
                        applyButton.setEnabled(false);
                        break;
                        
                }
        }
        
   
        
        public static void main(String [] args) throws InterruptedException{
                final ProgressModel model = new ProgressModel();
                model.addColumn(new ProgressModel.TitleColumn("Summary","1","2","3","4"));
                model.addColumn(new ProgressModel.ProcessColumn(4));
                model.addColumn(new ProgressModel.ProcessColumn(4));
                model.addColumn(new ProgressModel.ProcessColumn(4));
                String [] infoLabels = {"Processed","Closed: ","Unknown: ","Counter Example:","Errors:"};
              
                ProgressDialog dialog = new ProgressDialog(model,null,true,100,10,infoLabels,"","Z3","Simplify","Yices");
                dialog.setVisible(true);
                dialog.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
                
                for(int i=0; i< 1000; i++){
                        final int  p = i;
                        SwingUtilities.invokeLater(new Runnable() {
                                
                                @Override
                                public void run() {
                                        model.setProgress(p/10, 1, 2);
                                }
                        });
                        Thread.sleep(10);
                }
                model.setText("TIMEOUT", 1, 2);
                model.setEditable(true);
               
        }
}

class ProgressTable extends JTable{

        private static final long serialVersionUID = 1L;
        private static final int NUMBER_OF_VISIBLE_ROWS = 8;
        public interface ProgressTableListener{
                public void infoButtonClicked(int column, int row);
        }
        
        
        public static class ProgressPanel extends JPanel{
                private static final long serialVersionUID = 1L;
                private JProgressBar progressBar;
                private JButton      infoButton;
                
                private JProgressBar  getProgressBar(){
                        if(progressBar == null){
                                progressBar = new JProgressBar();
                                int height = getInfoButton().getMaximumSize().height;
                                progressBar.setMaximumSize(new Dimension(Integer.MAX_VALUE,height));
                                progressBar.setString("Test");
                                progressBar.setStringPainted(true);
                                progressBar.setFont(this.getFont());
                        }
                        return progressBar;
                }
                
                private JButton  getInfoButton(){
                        if(infoButton == null){                        	    
                                infoButton = new JButton("Info");
                                infoButton.setFont(this.getFont());
                                
                                Dimension dim = new Dimension();
                                infoButton.setMargin(new Insets(0,0,0,0));
                                
                                dim.height = this.getFontMetrics(this.getFont()).getHeight()+2;
                                dim.width = dim.height*3;
                                    
                                infoButton.setMinimumSize(dim);
                                infoButton.setPreferredSize(dim);
                                infoButton.setMaximumSize(dim);
                        
                        }
                        return infoButton;
                }
                ProgressPanel(){
                        
                        this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
                        this.add(Box.createVerticalStrut(2));
                        Box content = Box.createHorizontalBox();
                        content.add(Box.createHorizontalStrut(2));
                        content.add(getProgressBar());
                        content.add(Box.createHorizontalStrut(2));
                        content.add(getInfoButton());
                        content.add(Box.createHorizontalStrut(2));
                        this.add(content);
                        this.add(Box.createVerticalStrut(2));
                }
                public void setValue(int value){
                        getProgressBar().setValue(value);
                }
                
                public void setText(String text){
                        getProgressBar().setString(text);
                        getProgressBar().setStringPainted(text != null && !text.isEmpty() );
                }
        }
        
        
        
        
        private final ProgressPanel progressPanelRenderer = new ProgressPanel();
        private  ProgressPanel progressPanelEditor ;
 
        

        private class ProgressCellEditor extends AbstractCellEditor implements
                                                TableCellEditor{

                private static final long serialVersionUID = 1L;



                @Override
                public Component getTableCellEditorComponent(JTable table,
                                Object value, boolean isSelected, int row,
                                int column) {
                        
                        currentEditorCell.x = column;
                        currentEditorCell.y = row;
                        ProcessData data = (ProcessData) value;
                        prepareProgressPanel(getProgressPanelEditor(), data);
                        return getProgressPanelEditor();
                }
                
                

                @Override
                public Object getCellEditorValue() {
                            return null;
                }
                
        }
        
  
        
        
        
        private void prepareProgressPanel(ProgressPanel panel,final ProcessData data){
                panel.setValue(data.getProgress());
                panel.setText(data.getText());
                panel.infoButton.setEnabled(data.isEditable());
                panel.progressBar.setBackground(data.getBackgroundColor());
                panel.progressBar.setForeground(data.getForegroundColor());
                panel.progressBar.setUI(  new BasicProgressBarUI() {
                        
                    
                        @Override
                        protected Color getSelectionForeground() {
                              return  data.getSelectedTextColor();
                        }
                        
                        protected Color getSelectionBackground() { return data.getTextColor(); }
                        });
                                    
        }
        
        private final TableCellRenderer renderer = new TableCellRenderer() {
                
                @Override
                public Component getTableCellRendererComponent(JTable table,
                                Object value, boolean isSelected, boolean hasFocus,
                                int row, int column) {
                        ProcessData data = (ProcessData) value;
                        prepareProgressPanel(progressPanelRenderer, data);
                        return progressPanelRenderer;
                }
        };
        
        
        private final TableCellEditor editor = new ProgressCellEditor();
        private Point  currentEditorCell = new Point();
  
  
        
        public ProgressTable(int resolution, ProgressTableListener listener,String ...titles ) {
                this.setDefaultRenderer(ProgressModel.ProcessColumn.class,
                                renderer);
                this.setDefaultEditor(ProgressModel.ProcessColumn.class, editor);
                init(getProgressPanelEditor(),this.getFont(),resolution,listener);
                init(progressPanelRenderer,this.getFont(),resolution,listener);
          
        }
        
        private void init(ProgressPanel panel, Font font, int resolution, final  ProgressTableListener listener){
                panel.setFont(font);
                panel.progressBar.setMaximum(resolution);
                panel.infoButton.addActionListener(new ActionListener() {
                        
                        @Override
                        public void actionPerformed(ActionEvent e) {
                                listener.infoButtonClicked(currentEditorCell.x-1, currentEditorCell.y);
                                
                        }
                });
                
                
        }
        

        public void setModel(ProgressModel model, String ... titles){
        
                assert titles.length == model.getColumnCount();
                super.setModel(model);
                for(int i=0; i < titles.length; i++){
                        TableColumn col = getTableHeader().getColumnModel().getColumn(i);

                        col.setHeaderValue(titles[i]);   
                        packColumn(this, i,5);
                      
                }
                for(int i =0; i < model.getRowCount(); i++){
                        this.setRowHeight(progressPanelRenderer.getPreferredSize().height+5);
                }
                
                
               
        }
        
//        @Override
//        public Dimension getPreferredSize() {
//                Dimension dim = new Dimension(super.getPreferredSize());
//                dim.height = Math.min(NUMBER_OF_VISIBLE_ROWS * (progressPanelRenderer.getPreferredSize().height+5), dim.height);
//                return dim;
//        }
        
        @Override
        public Dimension getPreferredScrollableViewportSize() {
                Dimension dim = new Dimension(super.getPreferredScrollableViewportSize());
                
                dim.height = Math.min(NUMBER_OF_VISIBLE_ROWS * (progressPanelRenderer.getPreferredSize().height+5), dim.height);
                return dim;
        }
        
        public static void packColumn(JTable table, int vColIndex, int margin) {
               
                TableColumnModel colModel = table.getColumnModel();
                TableColumn col = colModel.getColumn(vColIndex);
                int width = 0;

  
                TableCellRenderer renderer = col.getHeaderRenderer();
                if (renderer == null) {
                    renderer = table.getTableHeader().getDefaultRenderer();
                }
                Component comp = renderer.getTableCellRendererComponent(
                    table, col.getHeaderValue(), false, false, 0, 0);
                width = comp.getPreferredSize().width;

        
                for (int r=0; r<table.getRowCount(); r++) {
                    renderer = table.getCellRenderer(r, vColIndex);
                    comp = renderer.getTableCellRendererComponent(
                        table, table.getValueAt(r, vColIndex), false, false, r, vColIndex);
                    width = Math.max(width, comp.getPreferredSize().width);
                }


                width += 2*margin;

                col.setPreferredWidth(width);
            }
        

        
        private ProgressPanel getProgressPanelEditor(){
                if(progressPanelEditor == null){
                        progressPanelEditor = new ProgressPanel();
                }
                return progressPanelEditor;
        }
      
        
        @Override
        public void tableChanged(TableModelEvent e) {
                if(e.getType() == TableModelEvent.UPDATE){
                        this.repaint();
             
                }
                super.tableChanged(e);
        }
        
}