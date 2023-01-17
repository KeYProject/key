package sourcerer.view;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import recoder.ModelElement;
import sourcerer.Main;
import sourcerer.Resources;
import sourcerer.SelectionModel;
import bsh.EvalError;
import bsh.Interpreter;

/*
   activate buttons
*/
public class BeanShellView extends ElementSelector {

    Console console;

    JScrollPane outputPane;
    JButton usageButton = new JButton("Usage");
    JButton clearButton = new JButton("Clear");
    
    public BeanShellView(Main m) {
	super(m.getModel(), "BeanShell Console", true);
	console = new Console(m.getServiceConfiguration()) {
		protected void processCommand(Interpreter interpreter, String command) { 
		    Object sel;
		    try {
			interpreter.eval(command);
			sel = interpreter.get("sel");
		    } catch (EvalError ee) {
			error(ee.toString());
			sel = null;
		    }
		    if (getModel() != null && sel instanceof ModelElement) {
			ModelElement e = getModel().getSelectedElement();
			if (sel != e) {
			    getModel().setSelectedElement((ModelElement)sel);
			}
		    }   		    
		}
	    };

	outputPane = new JScrollPane(console);
	addCenterComponent(outputPane);
	JPanel p = new JPanel();
	p.add(usageButton);

	usageButton.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    JTextArea textArea = new JTextArea(15, 40);
		    textArea.setEditable(false);
		    textArea.setBackground(getBackground());
		    textArea.setLineWrap(true);
		    textArea.setText(Resources.BEAN_SHELL_SCRIPT);
		    textArea.setCaretPosition(0);
		    JOptionPane.showMessageDialog(null, new JScrollPane(textArea));
		}
	    });

	p.add(clearButton);
	clearButton.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    console.clear();
		}
	    });
	addNorthComponent(p);
	
	changeSelection();
	console.requestFocus();
    }

    /**
       Use setSelectionModel(null) to detach from the model.
     */
    public void setModel(SelectionModel model) {
	SelectionModel oldModel = getModel();
	if (oldModel != model) {
	    if (oldModel != null) {
		oldModel.removeChangeListener(getChangeListener());
	    }
	    if (model != null) {
		super.setModel(model);
		model.addChangeListener(getChangeListener());		
	    }
	    changeSelection();
	}
    }

    private ChangeListener changeListener = null;
    
    /*
      The superclass calls setModel in the constructor, which is
      a bad idea since the changeListener field is not yet initialized
      when BeanShellView.this.setModel is called.
      Hence, we have to use an access method instead.  Bad world.
     */
    private ChangeListener getChangeListener() {
	if (changeListener == null) {
	    changeListener = new ChangeListener() {
		    public void stateChanged(ChangeEvent e) {
			changeSelection();
		    }
		};
	}
	return changeListener;
    }

    public void modelUpdated(boolean selectionRemoved) {
	changeSelection();
    }

    private void changeSelection() {
	if (console != null) {
	    ModelElement e = getModel() == null ? null : 
		getModel().getSelectedElement();
	    try {
		console.getInterpreter().set("sel", e);
	    } catch (EvalError ee) {
		console.error(ee.toString());
	    }
	}
    }
  

}
