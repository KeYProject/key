package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Insets;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import javax.swing.AbstractAction;
import javax.swing.AbstractCellEditor;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
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




public class ProgressDialog extends JDialog{

        private static final long serialVersionUID = 1L;
        private final ProgressTable   table;
        private JButton  applyButton;
        private JButton  stopButton;
        private JScrollPane scrollPane;
        private JButton  infoButton;
        private JPopupMenu infoMenu;
        private JProgressBar progressBar;
        private final ProgressDialogListener listener;
        public enum Modus {stopModus,discardModus};
        private Modus modus = Modus.stopModus;
       
        
        public static interface ProgressDialogListener extends ProgressTableListener{
                public void applyButtonClicked();
                public void stopButtonClicked();
                public void discardButtonClicked();
                public void additionalInformationChosen(Object obj);
              
        }
     
     
        
  
        
        public ProgressDialog(ProgressModel model,ProgressDialogListener listener, 
                        int resolution, int progressBarMax,String[] labelTitles,String ... titles) {
                table = new ProgressTable(resolution,listener,labelTitles); 
                table.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
                table.setModel(model,titles);
                this.listener = listener;
                this.setLocationByPlatform(true);
                this.setTitle("SMT Interface");
             
                setDefaultCloseOperation(DISPOSE_ON_CLOSE);
                setModal(true);
                this.setLayout(new BoxLayout(this.getContentPane(),BoxLayout.Y_AXIS));
                Box buttonBox = Box.createHorizontalBox();
                Box contentBox = Box.createVerticalBox();
                
                buttonBox.add(getInfoButton());
                buttonBox.add(Box.createHorizontalGlue());
                buttonBox.add(getStopButton());
                buttonBox.add(Box.createHorizontalStrut(5));
                buttonBox.add(getApplyButton());
                contentBox.add(getProgressBar());
                contentBox.add(Box.createVerticalStrut(5));
                contentBox.add(getScrollPane());
                getProgressBar().setMaximum(progressBarMax);
                this.getContentPane().add(contentBox);
                this.getContentPane().add(Box.createVerticalStrut(5));
                this.getContentPane().add(buttonBox);
                this.getContentPane().add(Box.createVerticalStrut(5));
              
              
                this.pack();
        }
        
        
        public void setAdditionalInformation(String title,Color color, List<? extends Object> information){
                getInfoButton().setText(title);
                getInfoButton().setForeground(color);
                infoMenu = new JPopupMenu();
                Collections.sort(information,new Comparator<Object>() {

                        @Override
                        public int compare(Object o1, Object o2) {
                               
                                return o1.toString().compareTo(o2.toString());
                        }
                });
                for(final Object obj : information){
                     JMenuItem item = new JMenuItem(new AbstractAction(
                        obj.toString()) {
                        private static final long serialVersionUID = 1L;

                    @Override
                        public void actionPerformed(ActionEvent e) {
                            listener.additionalInformationChosen(obj);
                        }
                    });
                 
                    infoMenu.add(item);
                }
                getInfoButton().setVisible(true);
                
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
     
        
        private JButton getInfoButton(){
                if(infoButton == null){
                        infoButton = new JButton("Info");
                        infoButton.setVisible(false);
                        infoButton.addActionListener(new ActionListener() {
                                
                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        JPopupMenu menu = getInfoMenu();
                                        int width = Math.max(menu.getPreferredSize().width,infoButton.getWidth());
                                            menu.setPopupSize(width, menu.getPreferredSize().height);
                                            menu.show(infoButton,0 ,infoButton.getHeight());       
                                }
                        });
                }
                return infoButton;
        }
        
        private JPopupMenu getInfoMenu(){
                if(infoMenu == null){
                        infoMenu = new JPopupMenu();
                }
                return infoMenu;
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
                        applyButton.setEnabled(true);
                        break;
                case stopModus:
                        stopButton.setText("Stop");
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
                String [] infoLabels = {"Processed","Closed: ","Unkown: ","Counter Example:","Errors:"}; 
              
                ProgressDialog dialog = new ProgressDialog(model,null,100,10,infoLabels,"","Z3","Simplify","Yices");
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
               
                TableColumnModel colModel = (TableColumnModel)table.getColumnModel();
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





