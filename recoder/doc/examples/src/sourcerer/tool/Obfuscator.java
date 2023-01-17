package sourcerer.tool;

import java.awt.BorderLayout;
import java.util.ArrayList;
import java.util.List;

import javax.swing.JPanel;

import recoder.kit.Problem;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import sourcerer.Main;
import sourcerer.util.Wizard;
import sourcerer.view.SelectionView;
import application.Obfuscate;

public class Obfuscator extends SourcererWizard implements SelectionView {

    Obfuscate obf;

    static final String TITLE_HEADER = "Obfuscator";

    public Obfuscator(Main main) {
	super(main);
	setName(TITLE_HEADER);
	start(descriptionState);
    }

    State descriptionState = new State() {

	    JPanel panel = new JPanel(new BorderLayout());
	    
	    public void stateEntered(Wizard w) {
		w.getNextButton().setToolTipText("Find declarations to mangle");
		w.getNextButton().setEnabled(true);
		w.getFinishButton().setEnabled(false);
		w.setComponent(panel);
		panel.add(message, BorderLayout.NORTH);
		message.setText("This wizard mangles all methods, variables, classes and packages where this is possible.\n" + 
				"Start the analysis, or abort.");
		w.setComponent(panel);
	    }
	    
	    public State nextState() {
		return analysisState;
	    }
	};

    State analysisState = new State() {

	    List list;
	    JPanel panel = new JPanel(new BorderLayout());
	    
	    public void stateEntered(Wizard w) {
		if (list == null) {
		    panel.add(message, BorderLayout.NORTH);
		    w.setComponent(panel);
		    message.setText("Preparing...");

		    obf = new Obfuscate(xconfig);
		    disableButtons();
		    new Thread(new Runnable() {
			    public void run() {
				ProblemReport pr = obf.analyze();
				if (pr instanceof Problem) {
				    displayFailure(pr);
				} else {
				    displaySuccess();
				}
			    }}).start();
		}
	    }

	    private void displayFailure(ProblemReport pr) {
		getBackButton().setEnabled(false);
		getNextButton().setEnabled(false);
		getCancelButton().setEnabled(true);
		message.setText("Found a problem: " + pr.toString() + "\n" +
				"Abort.");		
	    }
	    
	    private void displaySuccess() {
		message.append("done\n");
		getNextButton().setEnabled(true);
	    }

	    public State nextState() {
		return transformationState;
	    }
	};
    

    State transformationState = new State() {
	    
	    public void stateEntered(Wizard w) {
		JPanel panel = new JPanel(new BorderLayout());
		w.setComponent(panel);
		List<TwoPassTransformation> trans = new ArrayList<TwoPassTransformation>(1);
		trans.add(obf);
		transform(panel, trans);
	    }

	    public State nextState() {
		return null;
	    }
	};
}

