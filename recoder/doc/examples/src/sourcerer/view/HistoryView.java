package sourcerer.view;

import java.util.ArrayList;

import javax.swing.DefaultListModel;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import recoder.ModelElement;
import sourcerer.SelectionModel;

public class HistoryView extends ListSelector {

    protected int maxEntryCount = 100;

    public HistoryView(SelectionModel model) {
	super(model, "Last Visits", new ArrayList<ModelElement>(), "%c %n %u %p", false, false);
	selectorList.setModel(new DefaultListModel());
	selectionModel.addChangeListener(changeListener);	
    }

    protected ChangeListener changeListener = new ChangeListener() {
	    public void stateChanged(ChangeEvent e) {
		ModelElement p = selectionModel.getSelectedElement();
		if (p == null || p == selectorList.getSelectedValue()) {
		    return;
		}
		DefaultListModel m = (DefaultListModel)selectorList.getModel();
		int s = m.getSize();
		if (s == 0 || m.getElementAt(s - 1) != p) {
		    while (s > maxEntryCount) {
			m.remove(--s);
		    }
		    m.add(0, p);
		    selectorList.setSelectedIndex(0);
		}
	    }
	};


    public void back() {
	int i = selectorList.getSelectedIndex();
	if (i == -1 || i == selectorList.getModel().getSize() - 1) {
	    return;
	}
	selectorList.setSelectedIndex(i + 1);	
	selectionModel.setSelectedElement((ModelElement)selectorList.getSelectedValue());	
    }

    public void forward() {
	int i = selectorList.getSelectedIndex();
	if (i == -1 || i == 0) {
	    return;
	}
	selectorList.setSelectedIndex(i - 1);	
	selectionModel.setSelectedElement((ModelElement)selectorList.getSelectedValue());	
    }

    public void setModel(SelectionModel model) {
	if (selectionModel != model) {
	    if (selectionModel != null) {
		selectionModel.removeChangeListener(changeListener);
	    }
	    selectionModel = model;
	    if (model != null) {
		model.addChangeListener(changeListener);
	    }
	}       
    }

    public void modelUpdated(boolean selectionRemoved) {
	DefaultListModel m = (DefaultListModel)selectorList.getModel();
	m.clear();
    }

}


