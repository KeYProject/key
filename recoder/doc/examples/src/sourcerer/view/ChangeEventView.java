package sourcerer.view;

import java.awt.Color;
import java.awt.Component;
import java.util.ArrayList;
import java.util.List;

import javax.swing.DefaultListCellRenderer;
import javax.swing.JList;
import javax.swing.ListCellRenderer;

import recoder.ModelElement;
import recoder.convenience.Format;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.service.AttachChange;
import recoder.service.ChangeHistoryEvent;
import recoder.service.ChangeHistoryListener;
import recoder.service.DetachChange;
import recoder.service.TreeChange;
import sourcerer.SelectionModel;

/**

*/
public class ChangeEventView extends ListSelector implements ChangeHistoryListener {

    private final static String DEFAULT_TITLE = "Last Changes";

    public ChangeEventView(SelectionModel model) {
	super(model, DEFAULT_TITLE, new SelectorList(model, new ArrayList<ModelElement>(), TREE_CHANGE_RENDERER, ELEMENT_SELECTOR), false);
    }
    
    public void modelChanged(ChangeHistoryEvent changes) {
	List<TreeChange> list = changes.getChanges();
	updateNonModelElementList(DEFAULT_TITLE, list);
    }

    public void modelUpdated(boolean selectionRemoved) {
	// do not disable anything
    }

    public final static SelectorList.ElementSelector ELEMENT_SELECTOR = new SelectorList.ElementSelector() {
	    public ModelElement getElementToSelect(Object selected) {
		TreeChange tc = (TreeChange)selected;
		if (tc instanceof AttachChange) {
		    return tc.getChangeRoot();
		} else {
		    return tc.getChangeRootParent();
		}
	    }
	};

    public final static ListCellRenderer TREE_CHANGE_RENDERER = new DefaultListCellRenderer() {

	    StringBuffer buffer = new StringBuffer();

	    public Component getListCellRendererComponent
		(JList list, Object value, int index, 
		 boolean isSelected, boolean hasFocus) {	    
		super.getListCellRendererComponent
		    (list, value, index, isSelected, hasFocus);
		if (value instanceof TreeChange) {
		    TreeChange tc = (TreeChange)value;
		    if (tc.isMinor()) {
			setForeground(Color.gray);
		    } else {
			setForeground(Color.black);
		    }
		    buffer.setLength(0);
		    if (tc instanceof AttachChange) {
			buffer.append("Attached ");
		    } else if (tc instanceof DetachChange) {
			buffer.append("Detached ");
		    }
		    ProgramElement el = tc.getChangeRoot();
		    if (el instanceof CompilationUnit) {
			buffer.append(Format.toString("%c %u", el));
		    } else {
			buffer.append(Format.toString("%c @%p ", el));
			el = tc.getChangeRootParent();
			String format = "";
			if (tc instanceof AttachChange) {
			    format = "to ";
			} else {
			    format = "from ";
			}
			if (el instanceof CompilationUnit) {
			    format += "%c %u";
			} else {
			    format += "%c in %u";
			}
			buffer.append(Format.toString(format, el));
		    }
		    setText(buffer.toString());
		} else {
		    setText("");
		    setForeground(Color.black);
		}
		setIcon(null);
		return this;
	    }
	};
}

