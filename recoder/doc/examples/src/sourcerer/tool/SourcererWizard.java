package sourcerer.tool;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.List;

import javax.swing.BorderFactory;
import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.UIManager;

import recoder.CrossReferenceServiceConfiguration;
import recoder.kit.Transformation;
import recoder.kit.TwoPassTransformation;
import recoder.service.ChangeHistory;
import sourcerer.Main;
import sourcerer.SelectionModel;
import sourcerer.util.Wizard;
import sourcerer.view.ChangeEventView;
import sourcerer.view.SelectionView;

public abstract class SourcererWizard extends Wizard implements SelectionView {

    protected Main main;

    protected CrossReferenceServiceConfiguration xconfig;

    protected JTextArea message;

    public SourcererWizard(Main main) {

	this.main = main;
	xconfig = main.getServiceConfiguration();

	message = new JTextArea(3, 25);
	message.setEditable(false);
	message.setLineWrap(true);
	message.setWrapStyleWord(true);
	message.setBackground(getBackground());
	setMinimumSize(new Dimension(120, 120));

	getCancelButton().setIcon(UIManager.getIcon("InternalFrame.closeIcon"));
	getCancelButton().setToolTipText("Close wizard");
	getCancelButton().addActionListener(closeAction);
	getFinishButton().addActionListener(closeAction);
	setBorder(BorderFactory.createEmptyBorder(6, 3, 6, 3));
    }

    protected ActionListener closeAction = new ActionListener() {
	    public void actionPerformed(ActionEvent ee) {
		main.closeView(SourcererWizard.this);
	    }
	};

    protected void disableButtons() {
	getBackButton().setEnabled(false);
	getNextButton().setEnabled(false);
	getCancelButton().setEnabled(false);
	getFinishButton().setEnabled(false);
    }
    
    public SelectionModel getModel() {
	return main.getModel();
    }

    public void setModel(SelectionModel m) {
	// ignore
    }

    public void modelUpdated(boolean selectionRemoved) {}


    protected void transform(final JPanel panel, final List<TwoPassTransformation> transformations) {
	if (transformations == null || transformations.isEmpty()) {
	    return;
	}
	disableButtons();
	panel.add(message, BorderLayout.NORTH);
	message.setText("Performing changes...");
	new Thread(new Runnable() {
		public void run() {
		    for (int i = 0; i < transformations.size(); i += 1) {
			transformations.get(i).transform();
		    }
		    message.append("done\n");
		    ChangeEventView cev = new ChangeEventView(getModel());
		    message.append("Updating the model...");
		    ChangeHistory ch = xconfig.getChangeHistory();
		    ch.addChangeHistoryListener(cev);
		    ch.updateModel();
		    ch.removeChangeHistoryListener(cev);
		    panel.add(cev, BorderLayout.CENTER);
		    message.append("done\n");
		    message.append("You may visit the changes and undo or confirm them");
		    getFinishButton().setToolTipText("Confirm changes and close wizard");
		    getCancelButton().setToolTipText("Undo changes and close wizard");
		    getCancelButton().removeActionListener(closeAction);
		    getCancelButton().addActionListener(new ActionListener() {
			    public void actionPerformed(ActionEvent ae) {
				rollback(transformations);
			    }
			});
		    getCancelButton().setEnabled(true);
		    getFinishButton().setEnabled(true);
		}
	    }).start();
    }
    
    private void rollback(final List<? extends Transformation> transformations) {
	disableButtons();
	message.setText("Undoing changes...");
	new Thread(new Runnable() {
		public void run() {
		    for (int i = transformations.size() - 1; i >= 0; i -= 1) {
			transformations.get(i).rollback();
		    }
		    message.append("done\n");
		    message.append("Updating the model...");
		    ChangeHistory ch = xconfig.getChangeHistory();
		    ch.updateModel();
		    message.append("done\n");
		    main.closeView(SourcererWizard.this);
		}
	    }).start();
    }
    
}













