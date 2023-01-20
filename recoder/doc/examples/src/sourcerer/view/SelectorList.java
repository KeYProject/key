package sourcerer.view;

import java.util.List;

import javax.swing.AbstractListModel;
import javax.swing.JList;
import javax.swing.ListCellRenderer;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import recoder.ModelElement;
import recoder.convenience.Format;
import recoder.util.Order;
import recoder.util.Sorting;
import sourcerer.SelectionModel;
import sourcerer.util.ModelElementRenderer;

public class SelectorList extends JList {

    private SelectionModel selectionModel;

    public interface ElementSelector {
	ModelElement getElementToSelect(Object selectedItem);
    }

    private ElementSelector elementSelector = new ElementSelector() {
	    public ModelElement getElementToSelect(Object selectedItem) {
		return (ModelElement)selectedItem;
	    }	    
	};

    private void addListener() {
	addListSelectionListener(new ListSelectionListener() {
		public void valueChanged(ListSelectionEvent e) {
		    Object o = getSelectedValue();
		    if (o != null) {
			selectionModel.setSelectedElement(elementSelector.getElementToSelect(o));
		    }
		}
	    });
    }

    public SelectorList(SelectionModel model, final List list, ListCellRenderer renderer, final ElementSelector selector) {
	this.selectionModel = model;
	this.elementSelector = selector;
	setModel(new AbstractListModel() {
                public int getSize() { return list.size(); }
                public Object getElementAt(int i) { return list.get(i); }
            });
	setCellRenderer(renderer);	
	addListener();
    }

    public SelectorList(SelectionModel model, List<? extends ModelElement> list, final String format, boolean sort) {
	this.selectionModel = model;
	final Object[] a = list.toArray(new ModelElement[list.size()]);
	if (sort) {
	    Sorting.heapSort(a, new Order.Lexical() {
		    protected String toString(Object x) {
			return Format.toString(format, (ModelElement)x);
		    }
		});
	}
	setModel(new AbstractListModel() {
                public int getSize() { return a.length; }
                public Object getElementAt(int i) { return a[i]; }
            });
	setCellRenderer(new ModelElementRenderer(format));
	addListener();
    }
}
