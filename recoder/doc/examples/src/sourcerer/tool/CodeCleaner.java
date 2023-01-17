package sourcerer.tool;

import java.awt.BorderLayout;
import java.util.ArrayList;
import java.util.List;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.JCheckBox;
import javax.swing.JPanel;
import javax.swing.JScrollPane;

import recoder.ModelElement;
import recoder.kit.TwoPassTransformation;
import recoder.kit.transformation.RemoveRedundantTypeReferences;
import recoder.kit.transformation.RemoveUnusedImports;
import sourcerer.Main;
import sourcerer.util.Wizard;
import sourcerer.view.SelectorList;

public class CodeCleaner extends SourcererWizard {

    RemoveUnusedImports rui;
    RemoveRedundantTypeReferences rrtr;

    static final String TITLE_HEADER = "Code Cleaner";    

    public CodeCleaner(Main main) {
	super(main);
	setName(TITLE_HEADER);
	start(descriptionState);
    }

    State descriptionState = new State() {
	    
	    JPanel panel = new JPanel(new BorderLayout());
	    
	    public void stateEntered(Wizard w) {
		w.getNextButton().setToolTipText("Locate superfluous code");
		w.getNextButton().setEnabled(true);
		w.getFinishButton().setEnabled(false);
		w.setComponent(panel);
		panel.add(message, BorderLayout.NORTH);

		message.setText("This wizard locates and removes superfluous code.\n" + 
				"Change options and start the analysis, or abort.");
		JPanel options = new JPanel();
		options.setLayout(new BoxLayout(options, BoxLayout.Y_AXIS));
		JCheckBox importBox = new JCheckBox("Import statements", null, true);
		JCheckBox interfaceBox = new JCheckBox("Interface supertypes", null, true);
		JCheckBox exceptionBox = new JCheckBox("Exception declarations", null, true);
		JCheckBox typecastBox = new JCheckBox("Type casts", null, true);
		importBox.setEnabled(false);
		interfaceBox.setEnabled(false);
		exceptionBox.setEnabled(false);
		typecastBox.setEnabled(false);
		options.add(importBox);
		options.add(interfaceBox);
		options.add(exceptionBox);
		options.add(typecastBox);
		panel.add(options);
		// TODO: add options

		w.setComponent(panel);

	    }
	    
	    public State nextState() {
		return analysisState;
	    }
	};

    State analysisState = new State() {

	    List<ModelElement> list;
	    JPanel panel = new JPanel(new BorderLayout());
	    
	    public void stateEntered(Wizard w) {
		if (list == null) {
		    panel.add(message, BorderLayout.NORTH);
		    w.setComponent(panel);
		    message.setText("Analyzing system...");

		    rui = new RemoveUnusedImports(xconfig);
		    rrtr = new RemoveRedundantTypeReferences(xconfig);
		    disableButtons();
		    new Thread(new Runnable() {
			    public void run() {
				rui.addProgressListener(main.getStatusBar());
				rrtr.addProgressListener(main.getStatusBar());
				rui.analyze();
				rrtr.analyze();
				rrtr.removeProgressListener(main.getStatusBar());
				rui.removeProgressListener(main.getStatusBar());
				list = new ArrayList<ModelElement>(32);
				list.addAll(rui.getImportList());
				list.addAll(rrtr.getTypeReferenceList());
				getBackButton().setEnabled(true);
				getNextButton().setEnabled(true);
				getFinishButton().setEnabled(false);
				getCancelButton().setEnabled(true);
				
				display();
			    }}).start();
		} else {
		    display();
		}

	    }

	    private void display() {
		SelectorList s = new SelectorList(getModel(), list, "%c in %u @%4p", true);
		s.setBorder(BorderFactory.createEtchedBorder());
		panel.add(new JScrollPane(s), BorderLayout.CENTER);
		message.setText("Found " + list.size() + " code segments to clean.\n" + 
				"Go back to change settings, initiate removal, or abort.");
		getNextButton().setToolTipText("Remove superfluous code");
		getBackButton().setToolTipText("Back to description");
		getNextButton().setEnabled(!list.isEmpty());
		getFinishButton().setEnabled(list.isEmpty());
		if (list.isEmpty()) {
		    getFinishButton().setToolTipText("Nothing to be done");
		}
	    }
	    public State nextState() {
		return transformationState;
	    }
	};
    

    State transformationState = new State() {
	    
	    public void stateEntered(Wizard w) {
		JPanel panel = new JPanel(new BorderLayout());
		w.setComponent(panel);
		List<TwoPassTransformation> trans = new ArrayList<TwoPassTransformation>(2);
		trans.add(rui);
		trans.add(rrtr);
		transform(panel, trans);
	    }

	    public State nextState() {
		return null;
	    }
	};
   
}

