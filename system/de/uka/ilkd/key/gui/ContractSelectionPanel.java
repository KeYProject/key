package de.uka.ilkd.key.gui;

import java.awt.*;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;

import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.ContractSet;
import de.uka.ilkd.key.proof.mgt.OldOperationContract;
import de.uka.ilkd.key.proof.mgt.ProofStatus;

public class ContractSelectionPanel extends JPanel {
    
    static final Icon keyIcon = IconFactory.keyHole(20,20);
    static final Icon keyClosedIcon = IconFactory.keyHoleClosed(20,20);
    static final Icon keyAlmostClosedIcon = IconFactory.keyHoleAlmostClosed(20,20);

    
    private JList list;
    private JComponent comp;
    
    public ContractSelectionPanel(ContractSet ctSet, boolean dlchooser) {
        if(ctSet != null)
          list = new JList(sortContracts(ctSet));
	else
	  list = new JList();                       
        list.setSelectedIndex(0);
        if(!dlchooser) {
          list.setPreferredSize(new Dimension(800, list.getHeight()));
          comp = new JScrollPane(list);
	}else{
	  comp = list;
	}
        add(comp);
        list.setCellRenderer(new ContractListCellRenderer());        
    }
    
    public void setContracts(ContractSet ctSet) {
        remove(comp);
        list = new JList(sortContracts(ctSet));
        list.setSelectedIndex(0);
	comp = list;
        add(comp);
        list.setCellRenderer(new ContractListCellRenderer());        
    }

    private Object[] sortContracts(ContractSet ctSet) {
      Object[] cl = ctSet.toArray();
      Arrays.sort(cl, new ContractComparator());
      return cl;
    }
    
    public Contract getCurrentSelection() {
        if (list.getSelectedIndex()<0) {
            return null;
        }
        return (Contract) list.getSelectedValue();
    }
    
    public void addListSelectionListener(ListSelectionListener listener) {
        list.addListSelectionListener(listener);
    }
    
    
    class ContractListCellRenderer extends DefaultListCellRenderer {
        
        JPanel panel;
        JLabel text;
        private Color selBgColor;
	
        public ContractListCellRenderer() {
            setOpaque(true);
            FlowLayout lay = new FlowLayout();
            lay.setAlignment(FlowLayout.LEFT);              
            panel = new JPanel(lay);
            text = new JLabel();
            panel.add(text);
        }
        
        public Component getListCellRendererComponent(
            JList list,
            Object value,
            int index,
            boolean isSelected,
            boolean cellHasFocus)
        {   
            if (value instanceof OldOperationContract) {
                if (isSelected && selBgColor==null) {
                    Component sup = super.getListCellRendererComponent
                        (list, value, index, isSelected, cellHasFocus);
                    selBgColor = sup.getBackground();
                }                
                OldOperationContract mc = (OldOperationContract) value;
                text.setText(mc.getHTMLText());                
                panel.setBorder(new StatusTitledBorder(BorderFactory.createEtchedBorder(), 
                                                           mc.getName(), value));             
                text.setVerticalAlignment(SwingConstants.TOP);
                           if (isSelected) {
                    text.setBackground(selBgColor);
                    panel.setBackground(selBgColor);
                } else {
                    text.setBackground(Color.white);
                    panel.setBackground(Color.white);
                }
            } else {
                return super.getListCellRendererComponent(
                        list,value,index,isSelected,cellHasFocus);
            }            
            return panel;
        }
    }
    
    class StatusTitledBorder extends TitledBorder {
        
        private Object value;
        
        StatusTitledBorder(Border b, String s, Object value) {
            super(b,s);
            this.value = value;
        }
        
        
        public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
            title = "     "+title;
            super.paintBorder(c, g, x, y, width, height);
            List proofs = ((OldOperationContract)value).getProofs();
            Iterator it = proofs.iterator();
            while (it.hasNext()) {
                ProofAggregate pl = (ProofAggregate) it.next();
                ProofStatus ps = pl.getStatus();
                x=x+6;
                g.setColor(c.getBackground());
                g.fillRect(x, y, keyClosedIcon.getIconWidth(), 
                        keyClosedIcon.getIconHeight());
                if (ps.getProofClosedButLemmasLeft()) {
                    keyAlmostClosedIcon.paintIcon(c, g, x, y);
                } else if (ps.getProofClosed()) {
                    keyClosedIcon.paintIcon(c, g, x, y);
                } else if (ps.getProofOpen()) {
                    keyIcon.paintIcon(c, g, x, y);
                } 
            }                     
        }
      
    }
            
    private class ContractComparator implements Comparator {
      public int compare(Object o1, Object o2) {
        if(!(o1 instanceof Contract & o2 instanceof Contract))
	  return 0;
	return ((Contract)o1).getName().compareTo(((Contract)o2).getName());
      }
    }
    

}

    
