// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.lemmatagenerator;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.DefaultListSelectionModel;
import javax.swing.JButton;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTextField;
import javax.swing.RowFilter;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableRowSorter;

import de.uka.ilkd.key.gui.lemmatagenerator.ItemChooser.ItemFilter;
import de.uka.ilkd.key.gui.lemmatagenerator.SelectionPanel.Side;

import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletInfo;


/**
 * The panel ItemChooser offers the user the possibility to select certain items
 * a list. It consists of two tables. The one offers a list of items the user can choose 
 * (<code>suppliedItems</code>).
 * The other list shows the items that already have been chosen (<code>selectedList</code>).
 * Both table work on the same model, but with different filters. For that purpose the item 
 * is wrapped by an object of type TableItem. Each table item consists of the item to be presented 
 * and the information in which of both tables it should be shown.
 *  */



class ItemChooser<T> extends JPanel {

        private static final long serialVersionUID = 1L;
        private SelectionPanel<T> suppliedList;
        private SelectionPanel<T> selectedList;
        private JPanel middlePanel;
        private JPanel contentPanel;
        private JButton leftButton;
        private JButton rightButton;
        private List<TableItem<T>> items = new LinkedList<TableItem<T>>();
        private final List<ItemFilter<T>> filtersForMovingItems = new LinkedList<ItemChooser.ItemFilter<T>>();
        private final String searchTitle;
        // this data structure is shared with suppliedList and selectedList.
        private final List<ItemFilter<T>> userFilter = new LinkedList<ItemFilter<T>>();
      

        public interface ItemFilter<T>{
                boolean include(T itemData);
        }
       



        static private final Dimension MAX = new Dimension(Integer.MAX_VALUE,
                        Integer.MAX_VALUE);

        ItemChooser(String searchTitle) {
                this.searchTitle = searchTitle;
                this.setMaximumSize(MAX);
                setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
                add(Box.createVerticalStrut(10));
                add(getContentPanel());
                add(Box.createVerticalStrut(10));
          
        }
        
        public ItemChooser() {
                this("Search for items containing...");
        }

        private JPanel getContentPanel() {
                if (contentPanel == null) {
                        contentPanel = new JPanel();
                        contentPanel.setLayout(new BoxLayout(contentPanel,
                                        BoxLayout.X_AXIS));
                        contentPanel.add(getSuppliedList());
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
                                  cut(getSelectedList(),getSuppliedList());
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
                                        cut(getSuppliedList(),getSelectedList());

                                }
                        });
                }
                return rightButton;

        }
        


        private void cut(SelectionPanel<T> srcList, SelectionPanel<T> destList) {
                List<TableItem<T>> tableItems = srcList.getSelectedItems();
                for(TableItem<T> item : tableItems){
                        boolean move = true;
                        for(ItemFilter<T> filter : filtersForMovingItems){
                                if(!filter.include(item.getData())){
                                    move = false;    
                                }
                        }
                        
                        if(move){
                                item.setSide(destList.getSide());
                        }
                }
                srcList.update();
                destList.update();
  
                
        }
        


        private SelectionPanel<T> getSuppliedList() {
                if (suppliedList == null) {
                        suppliedList = new SelectionPanel<T>("Choice",searchTitle,Side.LEFT,userFilter);
                              }
                return suppliedList;
        }
        
        private SelectionPanel<T> getSelectedList() {
                if (selectedList == null) {
                        selectedList = new SelectionPanel<T>("Selection",searchTitle,Side.RIGHT,userFilter);
                }
                return selectedList;
        }
        

        public void setItems(List<T> dataForItems, String columnName) {
                
                items = new LinkedList<TableItem<T>>();
              
                for (T info : dataForItems) {
                        items.add(new TableItem<T>(info,Side.LEFT));
                      
                }
                ItemModel model = new ItemModel(columnName);
                for(TableItem<T> item : items){
                        model.addRow(new Object[]{item});
                }
      
             
                
           
                getSuppliedList().setModel(model);
                getSelectedList().setModel(model);
                getSuppliedList().selectAll();

        }
        
    

        public List<T> getDataOfSelectedItems() {
                
                List<T> list = new LinkedList<T>();
                for (TableItem<T> item : items) {
                        if(item.getSide() == Side.RIGHT){
                                list.add(item.getData());
                        }
                }
                return list;
        }
        
        public void moveAllToLeft(){
                for (TableItem<T> item : items) {
                        item.setSide(Side.LEFT);
                }
                update();
        }
        
        public void moveAllToRight(){
                for (TableItem<T> item : items) {
                        item.setSide(Side.RIGHT);
                }
                update();
        }

        public void removeSelection() {
                getSelectedList().removeSelection();
                getSuppliedList().removeSelection();
        }
        
        public void addFilter(ItemFilter<T> filter){
                userFilter.add(filter);
                update();
        }
        
        public void removeFilter(ItemFilter<T> filter){
                userFilter.remove(filter);
                update();
        }
        
        public void addFilterForMovingItems(ItemFilter<T> filter){
                filtersForMovingItems.add(filter);
        }
        
        public void removeFilterForMovingItems(ItemFilter<T> filter){
                filtersForMovingItems.remove(filter);
        }
        
        
        public void update(){
                getSelectedList().update();
                getSuppliedList().update(); 
        }
}

class SelectionPanel<T> extends JPanel{
        static enum Side  {LEFT,RIGHT};
        private static final long serialVersionUID = 1L;
        private JTextField textField;
        private JTable list;
        private JScrollPane scrollPane;
        private final Side side;
        private RowFilter<ItemModel, Integer> filter;
        
        private String findPattern = "";
        private final List<ItemFilter<T>> userFilters;
        


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
        
        public SelectionPanel(String title,String searchTitle, Side side,List<ItemFilter<T>> filters) {
                this.side = side;
                this.userFilters = filters;
                createFilter();
                this.setLayout(new BoxLayout(this,BoxLayout.Y_AXIS));
                this.add(getScrollPane());
                this.add(Box.createVerticalStrut(5));
                Box box = Box.createHorizontalBox();
                //box.setFont(getTextField().getFont());
                TitledBorder border = BorderFactory.createTitledBorder(searchTitle);
                border.setTitleFont(getTextField().getFont());
                box.setBorder(border);
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
                        ItemModel model = new ItemModel("");
                        setModel(model);
                        
                        
                        
                }
                
 
                return list;
        }
        
        DefaultTableModel getModel(){
                return (DefaultTableModel)getList().getModel();
        }
        

        List<T> getSelectedValues(){
       
                LinkedList<T> infoList = new LinkedList<T>();
                for(int i : getList().getSelectedRows()){
                TableItem<T> item = ((TableItem<T>)getList().getValueAt(i, 0)); 
                      infoList.add(item.getData());  
                }
                return infoList;
        }
        
        List<TableItem<T>> getSelectedItems(){
                
                LinkedList<TableItem<T>> infoList = new LinkedList<TableItem<T>>();
                for(int i : getList().getSelectedRows()){
                        TableItem<T> item = ((TableItem<T>)getList().getValueAt(i, 0)); 
                      infoList.add(item);  
                }
                return infoList;
        }
        
        void setSelectionInterval(int anchor, int lead){
             getList().getSelectionModel().setSelectionInterval(anchor, lead);
        }
       
        
        void createFilter(){
                filter = new RowFilter<ItemModel,Integer>() {

                        @Override
                        public boolean include(
                                        javax.swing.RowFilter.Entry<? extends ItemModel, ? extends Integer> entry) {
                                TableItem<T> item = (TableItem<T>) entry.getModel().getValueAt(entry.getIdentifier(),0);
                                
                                for(ItemFilter<T> userFilter : userFilters){
                                        if(!userFilter.include(item.getData())){
                                                return false;
                                        }
                                }
                                                    
                                if(findPattern != ""){
                                        if(item.getNameLowerCase().indexOf(findPattern)==-1){
                                                return false;
                                        }
                                }
                                
                                return item.getSide() == side;
                        }
                                
                      };
    
        }
    
        
        void setModel(ItemModel model){
          
                
                getList().setSelectionModel(new DefaultListSelectionModel());
                TableRowSorter<ItemModel> sorter = new TableRowSorter<ItemModel>(model);
                getList().setModel(model);
                sorter.setMaxSortKeys(1);
                sorter.setSortsOnUpdates(true);
                
    
                sorter.setRowFilter(filter);
                sorter.setComparator(0, new Comparator<TableItem<T>>() {

                        @Override
                        public int compare(TableItem<T> o1, TableItem<T> o2) {
                               
                                return o1.getNameLowerCase().compareTo(o2.getNameLowerCase());
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
        
        public void update(){
                ((TableRowSorter<ItemModel>)getList().getRowSorter()).setRowFilter(filter);
        }

       
        
}

// SOME DATA STRUCTURES FOR THE ITEM CHOOSER.

class ItemModel extends DefaultTableModel{
        private static final long serialVersionUID = 1L;
        
        ItemModel(String columnName){
                this.addColumn(columnName);
             
        }
        
        @Override
        public Class<?> getColumnClass(int columnIndex) {
                return columnIndex == 0 ? TacletInfo.class : Boolean.class;
        }
}



class TableItem<T>{

        private final T data;
        private Side  side;
        private final String lowerCaseName;
        
        public TableItem(T data, Side side) {
                super();
                this.data = data;
                this.side = side;
                this.lowerCaseName = data.toString().toLowerCase();
        }
        public T getData() {
                return data;
        }
        public Side getSide() {
                return side;
        }
        public void setSide(Side side) {
                this.side = side;
        }
        
        public String getNameLowerCase(){
                return lowerCaseName;
        }
        
        @Override
        public String toString() {
                
                return data.toString();
        }
        
}