package sourcerer.view;

import java.awt.BorderLayout;
import java.awt.Component;

import javax.swing.JButton;
import javax.swing.JPanel;
import javax.swing.UIManager;

import sourcerer.SelectionModel;
import sourcerer.util.SwingUtils;

/**
   A selector for program elements.
   This is a controler rather than a view and it does not listen to the 
   model.
 */
public class ElementSelector extends JPanel implements SelectionView {

    protected JButton closeButton;

    private JPanel topPanel;

    protected SelectionModel selectionModel;

    /**
       Calls setModel.
     */
    public ElementSelector(SelectionModel model, 
			   String name, 
			   boolean closeable) {
	super(new BorderLayout());
	setModel(model);
	 // replace this (and "p") with a GridBagLayout?
	setBackground(UIManager.getColor("control"));
	if (closeable) {
	    topPanel = new JPanel(new BorderLayout());
	    closeButton = new SwingUtils.CloseButton();
	    closeButton.setToolTipText("Close this view");
	    JPanel p = new JPanel();
	    p.add(closeButton);
	    topPanel.add(p, BorderLayout.EAST);
	    add(topPanel, BorderLayout.NORTH);
	}
	setName(name);
    }	

    public void addNorthComponent(Component c) {
	if (topPanel == null) {
	    add(c, BorderLayout.NORTH);
	} else {
	    topPanel.add(c);
	}
    }

    public void addCenterComponent(Component c) {
	add(c);
    }

    public SelectionModel getModel() {
	return selectionModel;
    }

    public void setModel(SelectionModel m) {
	this.selectionModel = m;
    }

    public void modelUpdated(boolean selectionRemoved) {}

    public JButton getCloseButton() {
	return closeButton;
    }
}
