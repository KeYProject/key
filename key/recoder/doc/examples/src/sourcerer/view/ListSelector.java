package sourcerer.view;

import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.List;

import javax.swing.AbstractListModel;
import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.border.TitledBorder;

import recoder.ModelElement;
import recoder.NamedModelElement;
import recoder.abstraction.ProgramModelElement;
import recoder.convenience.Format;
import sourcerer.SelectionModel;
import sourcerer.util.RecoderUtils;

/**
   A selector for program element lists.
 */
public class ListSelector extends ElementSelector {

    protected SelectorList selectorList;
    protected JButton gotoButton;
    protected String listFormat;
    protected boolean sorting;

    public ListSelector(SelectionModel model, 
			String name, 
			List<? extends ModelElement> list, 
			final String listFormat, 
			boolean autoSort,
			boolean closeable) {
	this(model, name, list, listFormat, autoSort, null, null, closeable);
    }

    public ListSelector(final SelectionModel model, 
			String name, 
			List<? extends ModelElement> list, 
			final String listFormat, 
			boolean autoSort, 
			String originTitleFormat,
			final ModelElement origin,
			boolean closeable) {
	super(model, name, closeable);
	this.sorting = autoSort;
	this.listFormat = listFormat;
	init(new SelectorList(model, list, listFormat, sorting),
	     originTitleFormat, origin);
    }

    public ListSelector(final SelectionModel model, 
			String name, 
			SelectorList selector,
			boolean closeable) {
	super(model, name, closeable);
	init(selector, null, null);
    }

    static final Insets MEDIUM_INSETS = new Insets(2, 2, 2, 2);

    // static final Icon gotoButtonIcon = Resources.getIcon("goto.icon");

    public SelectorList getList() {
	return selectorList;
    }
	
    public static JButton createGotoButton(final SelectionModel model, 
					   final ModelElement element,
					   String format) {
	JButton gotoButton = new JButton(); // gotoButtonIcon
	gotoButton.setMargin(MEDIUM_INSETS);
	String value;	    
	if (format.equals("%N") && element instanceof ProgramModelElement) {
	    value = RecoderUtils.getNonTrivialFullName((ProgramModelElement)element);
	} else {
	    value = Format.toString(format, element);
	}
	gotoButton.setText(value);
	gotoButton.setEnabled(element != null);
	gotoButton.setHorizontalAlignment(JButton.LEFT);
	gotoButton.setHorizontalTextPosition(JButton.LEFT);
	gotoButton.setToolTipText("Visit this element");
	gotoButton.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    model.setSelectedElement(element);
		}
	    });
	return gotoButton;
    }

    private void init(SelectorList selector,
		      String originTitleFormat,
		      final ModelElement origin) {
	selectorList = selector;
	
	if (origin != null) {
	    String format = origin instanceof NamedModelElement ? "%N" : "%c";
	    JButton gotoButton = createGotoButton(selectionModel, origin, format);
	    JPanel gotoPanel = new JPanel(new BorderLayout());
	    gotoPanel.add(gotoButton);
	    String title = "(" + selectorList.getModel().getSize() + ") " + Format.toString(originTitleFormat, origin) ; 
	    gotoPanel.setBorder(BorderFactory.createTitledBorder(BorderFactory.createEmptyBorder(), title, TitledBorder.LEADING, TitledBorder.TOP, getFont()));
	    addNorthComponent(gotoPanel);
	}
	addCenterComponent(new JScrollPane(selectorList));
    }

    public void updateNonModelElementList(String name, final List list) {
	setName(name);
	selectorList.setModel(new AbstractListModel() {
                public int getSize() { return list.size(); }
                public Object getElementAt(int i) { return list.get(i); }
            });
	repaint();
    }

    public void update(String name, List<? extends ModelElement> list) {
	setName(name);
	Container scrollPane = selectorList.getParent();
	scrollPane.remove(selectorList);	
	selectorList = new SelectorList(selectionModel, list, listFormat, sorting);

	scrollPane.add(selectorList);
	repaint();
    }

    public void modelUpdated(boolean selectionRemoved) {
	selectorList.setEnabled(false);
    }

}

