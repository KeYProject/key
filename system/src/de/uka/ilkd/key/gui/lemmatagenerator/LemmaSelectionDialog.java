package de.uka.ilkd.key.gui.lemmatagenerator;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Collections;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeSet;
import java.util.Vector;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.DefaultListCellRenderer;
import javax.swing.DefaultListModel;
import javax.swing.DefaultListSelectionModel;
import javax.swing.DefaultRowSorter;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTextField;
import javax.swing.ListModel;
import javax.swing.ListSelectionModel;
import javax.swing.RowFilter;
import javax.swing.RowSorter;
import javax.swing.RowSorter.SortKey;
import javax.swing.ScrollPaneConstants;
import javax.swing.SortOrder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.event.ListDataEvent;
import javax.swing.event.ListDataListener;
import javax.swing.event.ListSelectionListener;
import javax.swing.plaf.basic.BasicTreeUI.SelectionModelPropertyChangeHandler;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableModel;
import javax.swing.table.TableRowSorter;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.lemmatagenerator.SelectionPanel.Side;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletFilter;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletInfo;

class SelectionPanel extends JPanel{
        static enum Side  {LEFT,RIGHT};
        private static final long serialVersionUID = 1L;
        private JTextField textField;
        private JTable list;
        private JScrollPane scrollPane;
        private final Side side;
        private RowFilter<TacletModel, Integer> filter;
        
        private String findPattern = "";
        private boolean showOnlySupportedTaclets = true;
        


        static private final Dimension MAX = new Dimension(Integer.MAX_VALUE,
                        Integer.MAX_VALUE);

        
        private JScrollPane getScrollPane() {
                if (scrollPane == null) {

                        scrollPane = new JScrollPane(
                                        getList(),
                                        ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
                                        ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
                        scrollPane.setMaximumSize(MAX);
                       
                }
                return scrollPane;
        }
        
        public SelectionPanel(String title, Side side) {
                this.side = side;
                createFilter();
                this.setLayout(new BoxLayout(this,BoxLayout.Y_AXIS));
                this.add(getScrollPane());
                this.add(Box.createVerticalStrut(5));
                Box box = Box.createHorizontalBox();
                box.setBorder(BorderFactory.createTitledBorder("Search for"));
                box.add(getTextField());
                this.add(box);
                this.setBorder(BorderFactory.createTitledBorder(title));
                
        }
  
        private JTextField getTextField(){
                if(textField == null){
                       textField = new JTextField(); 
                       textField.getDocument().addDocumentListener(new DocumentListener() {
                        
                        @Override
                        public void removeUpdate(DocumentEvent e) {search();               
                        }
                        
                        @Override
                        public void insertUpdate(DocumentEvent e) {search();}
                        
                        @Override
                        public void changedUpdate(DocumentEvent arg0) {}
                       });
                }
                return textField;
        }
        
        void setTaclets(List<TableItem> tableItems){
                TacletModel model = new TacletModel();
                for(TableItem item : tableItems){
                        model.addRow(new Object[]{item});
                }
                setModel(model);
        }
        
        
        void addItems(List<TacletInfo> infoList){
                for(TacletInfo info : infoList){
                        getModel().addRow(new Object[]{info});
                }
        }
        
        void selectAll(){
                getList().getSelectionModel().setSelectionInterval(0, getList().getRowCount()-1);
        }
        
        private void search(){
                findPattern = textField.getText().toLowerCase();
                update();
                

        }
        
        private JTable getList() {
                if (list == null) {
                        list = new JTable();
                        TacletModel model = new TacletModel();
                        setModel(model);
                        
                        
                        
                }
                
 
                return list;
        }
        
        DefaultTableModel getModel(){
                return (DefaultTableModel)getList().getModel();
        }
        
        List<TacletInfo> getSelectedValues(){
       
                LinkedList<TacletInfo> infoList = new LinkedList<TacletInfo>();
                for(int i : getList().getSelectedRows()){
                      infoList.add(((TableItem)getList().getValueAt(i, 0)).info);  
                }
                return infoList;
        }
        
        List<TableItem> getSelectedItems(){
                
                LinkedList<TableItem> infoList = new LinkedList<TableItem>();
                for(int i : getList().getSelectedRows()){
                      infoList.add(((TableItem)getList().getValueAt(i, 0)));  
                }
                return infoList;
        }
        
        void setSelectionInterval(int anchor, int lead){
             getList().getSelectionModel().setSelectionInterval(anchor, lead);
        }
       
        
        void createFilter(){
                filter = new RowFilter<TacletModel,Integer>() {

                        @Override
                        public boolean include(
                                        javax.swing.RowFilter.Entry<? extends TacletModel, ? extends Integer> entry) {
                                TableItem item = (TableItem) entry.getModel().getValueAt(entry.getIdentifier(),0);
                                
                                if((showOnlySupportedTaclets && item.info.isNotSupported()) ||
                                                (item.info.isNotSupported() && side == Side.RIGHT)){
                                        return false;
                                }
                                
                                if(findPattern != ""){
                                        if(item.info.getNameLowerCase().indexOf(findPattern)==-1){
                                                return false;
                                        }
                                }
                                
                                return item.side == side;
                        }
                                
                      };
    
        }
    
        
        void setModel(TacletModel model){
          
                
                getList().setSelectionModel(new DefaultListSelectionModel());
                TableRowSorter<TacletModel> sorter = new TableRowSorter<TacletModel>(model);
                getList().setModel(model);
                sorter.setMaxSortKeys(1);
                sorter.setSortsOnUpdates(true);
                
    
                sorter.setRowFilter(filter);
                sorter.setComparator(0, new Comparator<TableItem>() {

                        @Override
                        public int compare(TableItem o1, TableItem o2) {
                               
                                return o1.info.getNameLowerCase().compareTo(o2.info.getNameLowerCase());
                        }
                });

                getList().setRowSorter(sorter);
                sorter.toggleSortOrder(0);
        
        }
        
        public void removeSelection(){
                getList().clearSelection();
        }

        
        public Side getSide() {
                return side;
        }
        
        @SuppressWarnings("unchecked")
        public void update(){
                ((TableRowSorter<TacletModel>)getList().getRowSorter()).setRowFilter(filter);
        }

        public void setShowOnlySupportedTaclets(boolean val) {
               showOnlySupportedTaclets = val;
               update();
                
        }
        
        
        
        
}

class TacletModel extends DefaultTableModel{
        private static final long serialVersionUID = 1L;
        
        TacletModel(){
                this.addColumn("Taclets");
             
        }
        
        @Override
        public Class<?> getColumnClass(int columnIndex) {
                return columnIndex == 0 ? TacletInfo.class : Boolean.class;
        }
}

class TableItem{

        public final TacletInfo info;
        public Side  side;
        public TableItem(TacletInfo info, Side side) {
                super();
                this.info = info;
                this.side = side;
        }
        
        @Override
        public String toString() {
                
                return info.toString();
        }
        
}



class TacletChooser extends JPanel {

        private static final long serialVersionUID = 1L;
        private SelectionPanel tacletList;
        private SelectionPanel selectedList;
        private JPanel middlePanel;
        private JPanel contentPanel;
        private JButton leftButton;
        private JButton rightButton;
        private List<TableItem> items = new LinkedList<TableItem>();

       
       



        static private final Dimension MAX = new Dimension(Integer.MAX_VALUE,
                        Integer.MAX_VALUE);

        TacletChooser() {
                this.setMaximumSize(MAX);
                setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
                add(Box.createVerticalStrut(10));
                add(getContentPanel());
                add(Box.createVerticalStrut(10));
        }

        private JPanel getContentPanel() {
                if (contentPanel == null) {
                        contentPanel = new JPanel();
                        contentPanel.setLayout(new BoxLayout(contentPanel,
                                        BoxLayout.X_AXIS));
                        contentPanel.add(getTacletList());
                        contentPanel.add(Box.createHorizontalStrut(5));
                        contentPanel.add(getMiddlePanel());
                        contentPanel.add(Box.createHorizontalStrut(5));
                        contentPanel.add(getSelectedList());
                        contentPanel.add(Box.createHorizontalGlue());
                }
                return contentPanel;
        }


        

        private JPanel getMiddlePanel() {
                if (middlePanel == null) {
                        middlePanel = new JPanel();
                        middlePanel.setLayout(new BoxLayout(middlePanel,
                                        BoxLayout.Y_AXIS));
                        middlePanel.add(getLeftButton());
                        middlePanel.add(Box.createVerticalStrut(10));
                        middlePanel.add(getRightButton());
                        Dimension dim = getLeftButton().getPreferredSize();
                        dim.height = dim.height
                                        + 10
                                        + getRightButton().getPreferredSize().height;
                        middlePanel.setMaximumSize(dim);

                }
                return middlePanel;
        }

        private JButton getLeftButton() {
                if (leftButton == null) {
                        leftButton = new JButton("<");
                        leftButton.addActionListener(new ActionListener() {

                                @Override
                                public void actionPerformed(ActionEvent e) {
                                  cut(getSelectedList(),getTacletList());
                                }
                        });
                }
                return leftButton;

        }

        private JButton getRightButton() {
                if (rightButton == null) {
                        rightButton = new JButton(">");
                        rightButton.addActionListener(new ActionListener() {

                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        cut(getTacletList(),getSelectedList());

                                }
                        });
                }
                return rightButton;

        }
        


        private void cut(SelectionPanel srcList, SelectionPanel destList) {
                List<TableItem> tableItems = srcList.getSelectedItems();
                for(TableItem item : tableItems){
                        if(!item.info.isNotSupported() || !item.info.isAlreadyInUse()){
                                item.side = destList.getSide();
                        }
                }
                srcList.update();
                destList.update();
  
                
        }

        private SelectionPanel getTacletList() {
                if (tacletList == null) {
                        tacletList = new SelectionPanel("Choice",Side.LEFT);
                }
                return tacletList;
        }
        
        private SelectionPanel getSelectedList() {
                if (selectedList == null) {
                        selectedList = new SelectionPanel("Selection",Side.RIGHT);
                }
                return selectedList;
        }
        

        public void setTaclets(List<TacletInfo> taclets) {
                
                items = new LinkedList<TableItem>();
              
                for (TacletInfo info : taclets) {
                        items.add(new TableItem(info,Side.LEFT));
                      
                }
           
                getTacletList().setTaclets(items);
                getSelectedList().setTaclets(items);
                getTacletList().selectAll();

                //getTacletList().setSelectionInterval(0,model.getRowCount()-1);
        }
        
    

        public ImmutableSet<Taclet> getSelectedTaclets() {
                
                ImmutableSet<Taclet> set = DefaultImmutableSet.nil();
                for (TableItem item : items) {
                        if(item.side == Side.RIGHT && !item.info.isNotSupported()){
                                set = set.add(item.info.getTaclet());
                        }
                }
                return set;
        }
        
        public void allTo(Side side){
                for (TableItem item : items) {
                        item.side = side;
                }
                update();
        }

        public void removeSelection() {
                getSelectedList().removeSelection();
                getTacletList().removeSelection();
        }
        
        public void setShowOnlySupportedTaclets(boolean val){
                getTacletList().setShowOnlySupportedTaclets(val);
        }
        
        public void update(){
                getSelectedList().update();
                getTacletList().update(); 
        }
}

public class LemmaSelectionDialog extends JDialog implements TacletFilter {

        private static final long serialVersionUID = 1L;

        private JButton okayButton;
        private JCheckBox showSupported;
        private JButton cancelButton;
        private JPanel buttonPanel;
        private JPanel contentPanel;
        private TacletChooser tacletChooser;
    


        public LemmaSelectionDialog() {
                this.setTitle("Taclet Selection");
                this.setLayout(new BoxLayout(this.getContentPane(),
                                BoxLayout.X_AXIS));
                this.getContentPane().add(Box.createHorizontalStrut(10));
                this.getContentPane().add(getContentPanel());
                this.getContentPane().add(Box.createHorizontalStrut(10));
                this.setMinimumSize(new Dimension(300, 300));
                this.setLocationByPlatform(true);

                this.pack();

        }

        public ImmutableSet<Taclet> showModal(List<TacletInfo> taclets) {
                this.setModal(true);
                this.getTacletChooser().setTaclets(taclets);
                this.setVisible(true);
                return getTacletChooser().getSelectedTaclets();
        }
        
        private JCheckBox getShowSupported() {
                if(showSupported == null){
                        showSupported = new JCheckBox("Show only supported taclets.");
                        showSupported.setSelected(true);
                        showSupported.addActionListener(new ActionListener() {
                                
                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        getTacletChooser().setShowOnlySupportedTaclets(showSupported.isSelected());
                                        
                                }
                        });
                }
                return showSupported;
        }

        private JPanel getButtonPanel() {

                if (buttonPanel == null) {
                        buttonPanel = new JPanel();
                        buttonPanel.setLayout(new BoxLayout(buttonPanel,
                                        BoxLayout.X_AXIS));
                        buttonPanel.add(getShowSupported());
                        buttonPanel.add(Box.createHorizontalGlue());
                        buttonPanel.add(getOkayButton());
                        buttonPanel.add(Box.createHorizontalStrut(8));
                        
                        buttonPanel.add(getCancelButton());
                }
                return buttonPanel;
        }

        private JPanel getContentPanel() {
                if (contentPanel == null) {
                        contentPanel = new JPanel();
                        contentPanel.setLayout(new BoxLayout(contentPanel,
                                        BoxLayout.Y_AXIS));
                        contentPanel.add(Box.createVerticalStrut(10));
                        contentPanel.add(getTacletChooser());
                        contentPanel.add(getButtonPanel());
                        contentPanel.add(Box.createVerticalStrut(10));
                }
                return contentPanel;
        }

        private JButton getOkayButton() {
                if (okayButton == null) {
                        okayButton = new JButton("Okay");
                        okayButton.addActionListener(new ActionListener() {

                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        tacletsSelected();
                                }
                        });
                        okayButton.setPreferredSize(getCancelButton().getPreferredSize());
                }
                return okayButton;
        }
        


        private void tacletsSelected() {

                dispose();
        }

        private void cancel() {
                getTacletChooser().removeSelection();
                getTacletChooser().allTo(Side.LEFT);
                dispose();
        }

        private JButton getCancelButton() {
                if (cancelButton == null) {
                        cancelButton = new JButton("Cancel");
                        cancelButton.addActionListener(new ActionListener() {

                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        cancel();
                                }
                        });
                }
                return cancelButton;
        }

        private TacletChooser getTacletChooser() {
                if (tacletChooser == null) {
                        tacletChooser = new TacletChooser();
                }
                return tacletChooser;
        }

        @Override
        public ImmutableSet<Taclet> filter(List<TacletInfo> taclets) {

                return showModal(taclets);
        }

}
