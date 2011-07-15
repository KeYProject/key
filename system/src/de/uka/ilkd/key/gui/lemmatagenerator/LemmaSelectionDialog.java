package de.uka.ilkd.key.gui.lemmatagenerator;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Collections;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.List;
import java.util.Vector;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.DefaultListCellRenderer;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.ListModel;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.Border;
import javax.swing.border.TitledBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.event.ListDataEvent;
import javax.swing.event.ListDataListener;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader.TacletFilter;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader.TacletInfo;

class SelectionPanel extends JPanel{
        private JTextField textField;
        private JList list;
        private JScrollPane scrollPane;
        private ListDataListener listener = new ListDataListener() {
                
                @Override
                public void intervalRemoved(ListDataEvent e) {
                        reset();
                        
                }
                
                @Override
                public void intervalAdded(ListDataEvent e) {
                        reset();
                }
                
                @Override
                public void contentsChanged(ListDataEvent e) {
                        reset();
                }
        };

        private  int selectedIndex = -1;
        private void reset(){
                selectedIndex = -1;
        }
        static private final Dimension MAX = new Dimension(Integer.MAX_VALUE,
                        Integer.MAX_VALUE);
        private final JLabel label = new JLabel();
        private final DefaultListCellRenderer cellRenderer = new DefaultListCellRenderer() {

                private String createAdditonalInfo(TacletInfo info) {
                        String s = "";
                        if (info.isNotSupported()) {
                                return " (is not supported)";
                        }
                        if (info.isAlreadyInUse()) {
                                return " (is already in use)";
                        }
                        return s;
                }

                private static final long serialVersionUID = 1L;

                public Component getListCellRendererComponent(JList list,
                                Object value, int index, boolean isSelected,
                                boolean cellHasFocus)

                {
                        if (value instanceof TacletInfo) {
                                TacletInfo info = ((TacletInfo) value);
                                value = info.getTaclet().name().toString()
                                                + createAdditonalInfo(info);
                        }
                        Component comp = 
                        super.getListCellRendererComponent(list, value,
                                        index, isSelected, cellHasFocus);
                        if(index == selectedIndex){
                                comp.setForeground(Color.RED);
                        }else{
                                comp.setForeground(Color.BLACK);
                        }
                        
                        
                        return comp;
                }
        };
        
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
        
        public SelectionPanel(String title) {
              
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
        
        private void search(){
              
                Enumeration<TacletInfo>  en = (Enumeration<TacletInfo>) getModel().elements();
                String pattern = textField.getText();
                int index =0;
                while(en.hasMoreElements()){
                        TacletInfo info = en.nextElement();
                        if(info.getTaclet().name().toString().startsWith(pattern)){
                                selectedIndex = index;
                               
                                getList().scrollRectToVisible( getList().getCellBounds(index,
                                                Math.min(index+getList().getVisibleRowCount()-1,getModel().getSize()-1))  );
                                getList().repaint();
                                return;   
                        }
                        index++;
                }
                
        
        }
        
        private JList getList() {
                if (list == null) {
                        list = new JList();

                        list.setModel(new DefaultListModel());
                        list.setCellRenderer(cellRenderer);
                }
                return list;
        }
        
        DefaultListModel getModel(){
                return (DefaultListModel)getList().getModel();
        }
        
        Object[] getSelectedValues(){
             return   getList().getSelectedValues();
        }
        
        void setSelectionInterval(int anchor, int lead){
                getList().setSelectionInterval(anchor, lead);
        }
        
        void setSelectedIndices(int[] indices){
                getList().setSelectedIndices(indices);
        }
        
        void setModel(ListModel model){
                getModel().removeListDataListener(listener);
                model.addListDataListener(listener);
               getList().setModel(model);
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
                                        cut(getSelectedList()
                                                        .getSelectedValues(),
                                                        getSelectionModel(),
                                                        getTacletModel(),
                                                        getTacletList());
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

                                        cut(getTacletList().getSelectedValues(),
                                                        getTacletModel(),
                                                        getSelectionModel(),
                                                        getSelectedList());
                                }
                        });
                }
                return rightButton;

        }

        private void cut(Object[] values, DefaultListModel src,
                        DefaultListModel dest, SelectionPanel destList) {
                if (values.length == 0) {
                        return;
                }
                int added = 0;
                for (Object value : values) {
                        TacletInfo info = (TacletInfo) value;
                        if (!info.isAlreadyInUse() && !info.isNotSupported()) {
                                src.removeElement(value);
                                dest.addElement(value);
                                added++;
                        }

                }
                if (added > 0) {
                        destList.setSelectionInterval(dest.size() - added,
                                        dest.size() - 1);
                }
        }

        private SelectionPanel getTacletList() {
                if (tacletList == null) {
                        tacletList = new SelectionPanel("Choice");
                }
                return tacletList;
        }
        
        private SelectionPanel getSelectedList() {
                if (selectedList == null) {
                        selectedList = new SelectionPanel("Selection");
                }
                return selectedList;
        }

 

        private DefaultListModel getSelectionModel() {
                return (DefaultListModel) (getSelectedList().getModel());
        }

        private DefaultListModel getTacletModel() {
                return (DefaultListModel) (getTacletList().getModel());
        }

        public void setTaclets(List<TacletInfo> taclets) {

                DefaultListModel model = getTacletModel();
                for (TacletInfo info : taclets) {
                        model.addElement(info);
                }
                
                getTacletList().setModel(model);

                getTacletList().setSelectionInterval(0, taclets.size() - 1);
        }

        public ImmutableSet<Taclet> getSelectedTaclets() {

                Object[] selected = getSelectionModel().toArray();
                ImmutableSet<Taclet> set = DefaultImmutableSet.nil();
                for (Object obj : selected) {
                        set = set.add(((TacletInfo) obj).getTaclet());
                }
                return set;
        }

        public void removeSelection() {
                getSelectedList().setSelectedIndices(new int[0]);
                getTacletList().setSelectedIndices(new int[0]);
        }
}

public class LemmaSelectionDialog extends JDialog implements TacletFilter {

        private static final long serialVersionUID = 1L;

        private JButton okayButton;

        private JButton cancelButton;
        private JPanel buttonPanel;
        private JPanel contentPanel;
        private TacletChooser tacletChooser;
        private JTextField  findField;

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

        private JPanel getButtonPanel() {

                if (buttonPanel == null) {
                        buttonPanel = new JPanel();
                        buttonPanel.setLayout(new BoxLayout(buttonPanel,
                                        BoxLayout.X_AXIS));
                     
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
                Collections.sort(taclets,new Comparator<TacletInfo>() {

                        @Override
                        public int compare(TacletInfo o1, TacletInfo o2) {
                                if((o1.isNotSupported() || o1.isAlreadyInUse() )&& (!o2.isAlreadyInUse() && !o2.isNotSupported())){
                                        return 1;
                                }
                                if((o2.isNotSupported() || o2.isAlreadyInUse() )&& (!o1.isAlreadyInUse() && !o1.isNotSupported())){
                                        return -1;
                                }
                                return o1.getTaclet().name().toString().compareTo(o2.getTaclet().name().toString());
                        }
                });
                return showModal(taclets);
        }

}
