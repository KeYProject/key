package sourcerer.view;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;
import javax.swing.text.Highlighter.HighlightPainter;

import recoder.ModelElement;
import recoder.java.ProgramElement;
import recoder.java.SourceElement.Position;
import sourcerer.SelectionModel;
import sourcerer.util.RecoderUtils;

/**
   A source code view.
   The view adds itself as a listener to the selection model.
   When the view is closed, the model should be set to <CODE>null</CODE>
   to remove the model listener.
*/
public class SourceCodeView extends JPanel implements SelectionView {

    protected JTextArea textArea;

    protected SelectionModel model;
    
    private DefaultHighlighter high;
    private HighlightPainter painter;

    /**
       Shown root.
     */
    protected ProgramElement root;

    /**
       Not editable by default.
       Font is set to monospaced.       
     */
    public SourceCodeView() {
	super(new BorderLayout());
	textArea = new JTextArea(25, 40);
	
	textArea.setEditable(false);
	textArea.setFont(new Font("Monospaced", Font.PLAIN, textArea.getFont().getSize()));
	textArea.setHighlighter(high = new DefaultHighlighter());
	textArea.addMouseListener(new MouseAdapter() {
		public void mousePressed(MouseEvent e) {
		    if (model != null) {
			if ((e.getModifiers() & MouseEvent.BUTTON1_MASK) != 0) {
			    ProgramElement selected = 
				getElementAtOffset(textArea.viewToModel(e.getPoint()));
			    if (selected != null) {
				model.setSelectedElement(selected);
			    }
			}
		    }
		}
	    });
	add(new JScrollPane(textArea));
	setMinimumSize(new Dimension(320, 240));
    }

    public JTextArea getTextArea() {
	return textArea;
    }

    public SelectionModel getModel() {
	return model;
    }

    public void setModel(SelectionModel model) {
	if (this.model != model) {
	    if (this.model != null) {
		this.model.removeChangeListener(changeListener);
	    }
	    if (model != null) {
		model.addChangeListener(changeListener);
	    }
	    this.model = model;
	    this.root = null;
	    textArea.setText("");
	    changeSelection();
	}
    }

    public void modelUpdated(boolean selectionRemoved) {
	if (selectionRemoved) {
	    high.removeAllHighlights();
	}
	root = null; // enforce redisplay
	changeSelection();
    }

    private void changeSelection() {
	ModelElement element = getModel().getSelectedElement();
	if (!(element instanceof ProgramElement)) {
	    high.removeAllHighlights();
	    /*
	    if (element instanceof recoder.bytecode.ByteCodeElement) {
		textArea.setText("This element is represented in byte code.");
	    } else {	    
		textArea.setText("This element has no syntactic representation.");
		// No element selected.
	    }
	    */
	    textArea.setText("");
	    textArea.setVisible(false);
	    root = null;
	    return;
	} 
	textArea.setVisible(true);
	ModelElement newroot = getModel().getRoot();
	if (!(newroot instanceof ProgramElement)) {
	    root = null;
	    return;
	}
	if (newroot != root) {
	    root = (ProgramElement)newroot;
	    if (root == null) {
		textArea.setText("");
	    } else {
		textArea.setText(root.toSource());
		textArea.setCaretPosition(0);
	    }
	}
	highlight((ProgramElement)element);
    }

    protected ChangeListener changeListener = new ChangeListener() {
	    public void stateChanged(ChangeEvent e) {
		changeSelection();
	    }
	};

    public ProgramElement getElementAtOffset(int offset) {
	if (root == null) {
	    return null;
	}
	try {	    
	    int line = textArea.getLineOfOffset(offset);
	    int column = offset - textArea.getLineStartOffset(line);
	    return RecoderUtils.getElementAtPosition(root, line + 1, column + 1);
	} catch (BadLocationException ble) {
	    return null;
	}
    }

    protected boolean autoshow = true;

    public boolean isAutoShowing() {
	return autoshow;
    }

    public void setAutoShowing(boolean yes) {
	autoshow = yes;
    }

    public void highlight(ProgramElement element) {	
	// check feasibility
	Position pos = element.getFirstElement().getStartPosition();
	int line1 = pos.getLine() - 1;
	int col1 = pos.getColumn() - 1;
	pos = element.getLastElement().getEndPosition();
	int line2 = pos.getLine() - 1;
	int col2 = pos.getColumn() - 1;
	try {
	    int start = textArea.getLineStartOffset(line1) + col1;
	    int end = textArea.getLineStartOffset(line2) + col2;
	    high.removeAllHighlights();
	    if (painter == null) {
		painter = new DefaultHighlightPainter(null);
	    }
	    high.addHighlight(start, end, painter);
	    if (autoshow) {
		textArea.setCaretPosition(start);
	    }
	} catch (BadLocationException ble) {
	    return;
	}
    }
}
