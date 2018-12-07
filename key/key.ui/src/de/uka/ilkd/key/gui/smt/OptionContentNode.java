package de.uka.ilkd.key.gui.smt;

import javax.swing.JComponent;
import javax.swing.tree.DefaultMutableTreeNode;

public class OptionContentNode extends DefaultMutableTreeNode{
        private static final long serialVersionUID = 1L;
        private final JComponent component;
        
       
        public OptionContentNode(String title,JComponent component) {
                super();
                this.component = component;
                this.setUserObject(title);
        }

        public JComponent getComponent(){
                return component;
        }
                
}