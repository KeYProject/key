package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.Graphics;
import java.awt.Insets;
import java.awt.Rectangle;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.ArrayList;

import javax.swing.AbstractCellEditor;
import javax.swing.Action;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.SwingUtilities;
import javax.swing.event.TableModelEvent;
import javax.swing.event.TableModelListener;
import javax.swing.plaf.basic.BasicProgressBarUI;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;
import javax.swing.table.TableColumn;
import javax.swing.table.TableColumnModel;
import javax.swing.table.TableModel;

import de.uka.ilkd.key.gui.smt.ProgressModel.ProcessColumn.ProcessData;
import de.uka.ilkd.key.java.declaration.modifier.Model;




public class NewProgressDialog extends JDialog{

        private final ProgressTable   table;
        private JButton  applyButton;
        private JButton  stopButton;
        private JScrollPane scrollPane;
        private JTable captionTable;
        
        
     
     
        
  
        
        public NewProgressDialog(ProgressModel model,String[] labelTitles,String ... titles) {
                table = new ProgressTable(labelTitles); 
                table.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
             
                this.setLayout(new BoxLayout(this.getContentPane(),BoxLayout.Y_AXIS));
                Box buttonBox = Box.createHorizontalBox();
                Box contentBox = Box.createVerticalBox();
             
                buttonBox.add(Box.createHorizontalGlue());
                buttonBox.add(getStopButton());
                buttonBox.add(Box.createHorizontalStrut(5));
                buttonBox.add(getApplyButton());
                
                contentBox.add(getScrollPane());
                this.getContentPane().add(contentBox);
                this.getContentPane().add(buttonBox);
                
                table.setModel(model,titles);
              
                this.pack();
        }
        
     
        
        
        private JButton getApplyButton() {
                if(applyButton == null){
                       applyButton = new JButton("Apply");
                       
                }
                return applyButton;
        }
        
        private JScrollPane getScrollPane() {
                if(scrollPane == null){
                        scrollPane = new JScrollPane(table,JScrollPane.VERTICAL_SCROLLBAR_ALWAYS,
                                        JScrollPane.HORIZONTAL_SCROLLBAR_ALWAYS
                                        );
                        
                }
                return scrollPane;
        }
        
        private JButton getStopButton() {
                if(stopButton == null){
                        stopButton = new JButton("Stop");
                 }
                return stopButton;
        }
        
        
   
        
        public static void main(String [] args) throws InterruptedException{
                final ProgressModel model = new ProgressModel();
                model.addColumn(new ProgressModel.TitleColumn("Summary","1","2","3","4"));
                model.addColumn(new ProgressModel.ProcessColumn(4));
                model.addColumn(new ProgressModel.ProcessColumn(4));
                model.addColumn(new ProgressModel.ProcessColumn(4));
                String [] infoLabels = {"Processed","Closed: ","Unkown: ","Counter Example:","Errors:"}; 
              
                NewProgressDialog dialog = new NewProgressDialog(model,infoLabels,"","Z3","Simplify","Yices");
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
      
        public static class ProgressPanel extends JPanel{
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
                                infoButton = new JButton("i");
                                infoButton.setFont(this.getFont());
                                
                                Dimension dim = new Dimension();
                                infoButton.setMargin(new Insets(0,0,0,0));
                                
                                dim.height = this.getFontMetrics(this.getFont()).getHeight()+2;
                                dim.width = dim.height;
                                    
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
                        getProgressBar().setStringPainted(text != null && text != "" );
                }
        }
        
        
        public static class SummaryPanel extends JPanel{
          
                private JProgressBar      progressBar;
                private JTable       table;
                private final DefaultTableModel model    = new DefaultTableModel();
                private Color colors [] ;
                private final TableCellRenderer renderer = new DefaultTableCellRenderer() {
                        
                        @Override
                        public Component getTableCellRendererComponent(JTable table,
                                        Object value, boolean isSelected, boolean hasFocus,
                                        int row, int column) {
                                Component comp = super.getTableCellRendererComponent(table,value,
                                                isSelected, hasFocus,row,column);
                                comp.setForeground(colors[row]);
                                return comp;
                        }
                };
                
                SummaryPanel(String [] labelTitles){
                       // infoLabels = createInfoLabels(labelTitles,this.getFont());
                        this.setLayout(new BoxLayout(this, BoxLayout.X_AXIS));
                        this.add(Box.createHorizontalStrut(3));
                        Box content = Box.createVerticalBox();
                        content.add(Box.createVerticalStrut(5));
                        content.add(getProgressBar());
                        content.add(Box.createVerticalStrut(2));
                        content.add(getTable());
                        content.add(Box.createVerticalStrut(5));
                        colors = new Color[labelTitles.length];
                        
                        String values [] = new String[labelTitles.length];
                        for(int i=0; i < labelTitles.length; i++){
                                values[i] = "-";
                                colors[i] = Color.BLACK;
                        }
                        model.addColumn("",labelTitles);
                        model.addColumn("",values);
                     
                        getTable().setModel(model);
                        table.setAutoResizeMode(AUTO_RESIZE_OFF);
                    
                        table.getColumnModel().getColumn(0).setCellRenderer(renderer);
                        table.getColumnModel().getColumn(1).setCellRenderer(renderer);
                        int max=0;
                        for(int i=0; i < labelTitles.length; i++){
                                
                                int width = table.getFontMetrics(table.getFont()).stringWidth(labelTitles[i]);
                                max = max <  width? width :max; 
                        }
                        TableColumn col = getTable().getTableHeader().getColumnModel().getColumn(0);
                        col.setMinWidth(max+5);
                        col.setMaxWidth(max+5);        
                         col = getTable().getTableHeader().getColumnModel().getColumn(1);
                        col.setMinWidth(max/3);
                        table.setPreferredScrollableViewportSize(table.getPreferredSize());
                
                        this.add(content);
                        this.add(Box.createHorizontalStrut(3));
                }
                
                JTable getTable(){
                        if(table == null){
                                table = new JTable();
                                table.setShowVerticalLines(false);
                                
                               
                        }
                        return table;
                }
                
                JProgressBar getProgressBar(){
                        if(progressBar == null){
                                progressBar = new JProgressBar();
                        }
                        return progressBar;
                }
                
                public void setColor(int row, Color color){
                       colors[row] = color;  
                       table.repaint();
                }
                
                public void setValue(int row, String value){
                        model.setValueAt(value, row, 1);
                        table.repaint();
                }
       
        }
        
        private final ProgressPanel progressPanelRenderer = new ProgressPanel();
        private  ProgressPanel progressPanelEditor ;
        private final SummaryPanel summaryPanelRenderer;
        private class ProgressCellEditor extends AbstractCellEditor implements
                                                TableCellEditor{

                @Override
                public Component getTableCellEditorComponent(JTable table,
                                Object value, boolean isSelected, int row,
                                int column) {
                      
                        
                        ProcessData data = (ProcessData) value;
                        prepareProgressPanel(getProgressPanelEditor(), data);
                        return getProgressPanelEditor();
                }
                
                

                @Override
                public Object getCellEditorValue() {
                        // TODO Auto-generated method stub
                        return null;
                }
                
        }
        
        private ProgressModel progressModel = new ProgressModel();
        
        
        
        private void prepareProgressPanel(ProgressPanel panel,final ProcessData data){
                panel.setValue(data.getProgress());
                panel.setText(data.getText());
                panel.infoButton.setEnabled(data.isEditable());
                panel.progressBar.setBackground(data.getBackgroundColor());
                panel.progressBar.setForeground(data.getForegroundColor());
                panel.progressBar.setUI(  new BasicProgressBarUI() {
                        
                    
                        @Override
                        protected Color getSelectionForeground() {
                              return  data.getTextColor();
                        }
                        
                        protected Color getSelectionBackground() { return data.getTextColor(); }
                        });
                                    
        }
        
        private final TableCellRenderer renderer = new TableCellRenderer() {
                
                @Override
                public Component getTableCellRendererComponent(JTable table,
                                Object value, boolean isSelected, boolean hasFocus,
                                int row, int column) {
                        if(row == 0){
                           return summaryPanelRenderer;     
                        }
                        ProcessData data = (ProcessData) value;
                        prepareProgressPanel(progressPanelRenderer, data);
                        return progressPanelRenderer;
                }
        };
        
        
        private final TableCellEditor editor = new ProgressCellEditor();
        
  
        
        public ProgressTable(String ...titles ) {
                this.setDefaultRenderer(ProgressModel.ProcessColumn.class,
                                renderer);
                this.setDefaultEditor(ProgressModel.ProcessColumn.class, editor);
                progressPanelRenderer.setFont(this.getFont());
               // this.setRowHeight(40);
                //this.setRowHeight(0,100);
                summaryPanelRenderer = new SummaryPanel(titles);
               
             
        }
        

        public void setModel(ProgressModel model, String ... titles){
                this.progressModel = model;
                assert titles.length == model.getColumnCount();
                super.setModel(model);
                for(int i=0; i < titles.length; i++){
                        TableColumn col = getTableHeader().getColumnModel().getColumn(i);
                       
                        col.setHeaderValue(titles[i]);   
                      //  col.setMinWidth(400);
                        //col.setWidth(col.getPreferredWidth());
                      //  col.sizeWidthToFit();
                        packColumn(this, i,5);
                       
                }
                for(int i =0; i < model.getRowCount(); i++){
                        this.setRowHeight(i,i == 0 ? summaryPanelRenderer.getPreferredSize().height : 40);
                }
                
                
               
        }
        
        public static void packColumn(JTable table, int vColIndex, int margin) {
               
                TableColumnModel colModel = (TableColumnModel)table.getColumnModel();
                TableColumn col = colModel.getColumn(vColIndex);
                int width = 0;

                // Get width of column header
                TableCellRenderer renderer = col.getHeaderRenderer();
                if (renderer == null) {
                    renderer = table.getTableHeader().getDefaultRenderer();
                }
                Component comp = renderer.getTableCellRendererComponent(
                    table, col.getHeaderValue(), false, false, 0, 0);
                width = comp.getPreferredSize().width;

                // Get maximum width of column data
                for (int r=0; r<table.getRowCount(); r++) {
                    renderer = table.getCellRenderer(r, vColIndex);
                    comp = renderer.getTableCellRendererComponent(
                        table, table.getValueAt(r, vColIndex), false, false, r, vColIndex);
                    width = Math.max(width, comp.getPreferredSize().width);
                }

                // Add margin
                width += 2*margin;

                // Set the width
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

class ProgressModel extends AbstractTableModel{

        private static interface Column{
               Object getObject(int row);
               int    getRowCount();
               
               boolean   isEditable();
     
        }
        
        public static class TitleColumn implements Column{
                private final String []titles;
                
                public TitleColumn( String ... titles) {
                        super();
                        this.titles = titles;
                  
                }
                
                

                @Override
                public Object getObject(int row) {
                         return titles[row];
                }

                @Override
                public int getRowCount() {
                        
                        return titles.length;
                }


                @Override
                public boolean isEditable() {
                 
                        return false;
                }   
                
        }
        
        public static class ProcessColumn  implements Column{
          
                static class ProcessData{
                        private  int   progress=0;
                        private  String text="";
                        private boolean isEditable = false;
                        private Color textColor = Color.RED;
                        private Color backgroundColor = Color.WHITE;
                        private Color foregroundColor = Color.BLUE;
                  
                        public int getProgress() {
                                return progress;
                        }
                        public String getText() {
                                return text;
                        }
                  
                        public boolean isEditable() {
                                return isEditable;
                        }
                        
                        public Color getBackgroundColor() {
                                return backgroundColor;
                        }
                        
                        public Color getTextColor() {
                                return textColor;
                        }
                        
                        public Color getForegroundColor() {
                                return foregroundColor;
                        }
                        
                }
                
             //   private final Object [] processes;           
                public final ProcessData []  data;
                private boolean isEditable = false;
                
                
                public ProcessColumn(int size) {
                        super();
                        
                        
                        this.data = new ProcessData[size+1];
                    
                        for(int i=0; i < data.length; i++){
                                data[i] = new ProcessData();
                                
                                                }
                        
                }

                

                @Override
                public Object getObject(int row) {
                      // if(row == 0){return title;}
                       //progressBar.setValue(progress[row-1]);
                       return data[row];
                }
                
                public void setProgress(int value, int row){
                        data[row].progress = value;
                }
                
                public void setText(String value, int row){
                        data[row].text = value;
                }
                
                
                @Override
                public int getRowCount() {
                        
                        return data.length;
                }


                public void setEditable(boolean b) {
                      isEditable = b;  
                      for(int i=0; i < data.length; i++){
                              data[i].isEditable = b;
                      }
                }



                @Override
                public boolean isEditable() {
                   
                        return isEditable;
                }   
                
        }
        
        private ArrayList<Column> columns = new ArrayList<Column>();
        
        private int rowCount=-1;
        
        
        
        public ProgressModel() {
                super();
                
        }
        
        public void addColumn(Column column) {
             if(rowCount != -1 && rowCount != column.getRowCount()){
                     throw new IllegalArgumentException("Columns must have the same number of rows.");
             }
             rowCount = column.getRowCount();
             columns.add(column);
        }
        
        public void setProgress(int value, int column, int row){
                column++;
                row++;
                ProcessColumn col = (ProcessColumn)columns.get(column);
                col.setProgress(value, row);
                this.fireTableCellUpdated(row, column);
        }
        
        public void setText(String text, int column, int row){
                column++;
                row++;
                ProcessColumn col = (ProcessColumn)columns.get(column);
                col.setText(text,row);
                this.fireTableCellUpdated(row, column);
        }
        
        public void setTextColor(Color color, int x, int y) {
                x++; y++;
                ProcessColumn col = (ProcessColumn)columns.get(x);
                col.data[y].textColor = color;
                
                this.fireTableCellUpdated(x, y);
        }
        
        public void setForegroundColor(Color color, int x, int y) {
                x++; y++;
                ProcessColumn col = (ProcessColumn)columns.get(x);
                col.data[y].foregroundColor = color;
                
                this.fireTableCellUpdated(x, y);
        }
        
        public void setBackgroundColor(Color color, int x, int y) {
                x++; y++;
                ProcessColumn col = (ProcessColumn)columns.get(x);
                col.data[y].backgroundColor = color;
                
                this.fireTableCellUpdated(x, y);
        }
        
        public void setEditable(boolean b){
                for(Column column : columns){
                      if(column instanceof ProcessColumn){
                              ((ProcessColumn) column).setEditable(b);
                      }
                }
        }

        @Override
        public int getColumnCount() {
              
                return columns.size();
        }

        @Override
        public int getRowCount() {
                
                return rowCount;
        }
        
        @Override
        public boolean isCellEditable(int rowIndex, int columnIndex) {
                
                return rowIndex != 0 && columns.get(columnIndex).isEditable();
        }
        
        
        
        @Override
        public Class<?> getColumnClass(int columnIndex) {
                return columns.get(columnIndex).getClass();

        }

        @Override
        public Object getValueAt(int row, int col) {
                
                return columns.get(col).getObject(row);
        }
        
        public Column getColumn(int col){
                return columns.get(col);
        }
        
        
        
}





