package sourcerer.util;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Stack;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;

import sourcerer.Resources;

/**
   Wizard base class.
   A wizard is a sequence of (possibly infinite) states that
   offer user interactions.
*/
public class Wizard extends JPanel {

    private JButton nextButton;
    private JButton backButton;
    private JButton finishButton;
    private JButton cancelButton;
    private Stack states;
    private Component component;
    
    /**
       Initializes a new wizard with buttons at the SOUTH area of the panel.
     */    
    public Wizard() {
	this(BorderLayout.SOUTH);
    }

    /**
       Initializes a new wizard. Call start() to invoke the state transitions.
       @param buttonPosition a border layout position (should not be CENTER).
     */    
    public Wizard(String buttonPosition) {
	super(new BorderLayout());

	Insets minMargin = new Insets(2, 2, 2, 2);
	nextButton = new JButton("Next", Resources.FORWARD_ICON);
	nextButton.setHorizontalTextPosition(JButton.LEFT);
	nextButton.setMnemonic('n');
	nextButton.setMargin(minMargin);
	backButton = new JButton("Back", Resources.BACK_ICON);
	backButton.setMnemonic('b');
	backButton.setMargin(minMargin);
	cancelButton = new JButton("Cancel");
	cancelButton.setMnemonic('c');
	cancelButton.setMargin(minMargin);
	finishButton = new JButton("Finish");
	finishButton.setMnemonic('f');
	finishButton.setMargin(minMargin);
	
	nextButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
		backButton.setEnabled(true);
		State s = getCurrentState().nextState();
		states.push(s);
		s.stateEntered(Wizard.this);
	    }
	});
	backButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
		states.pop();
		backButton.setEnabled(states.size() > 1);
		getCurrentState().stateEntered(Wizard.this);
	    }
        });

	JPanel buttons = new JPanel(new javax.swing.plaf.basic.BasicOptionPaneUI.ButtonAreaLayout(true, 6));
	buttons.add(backButton);
	buttons.add(nextButton);
	buttons.add(finishButton);
	buttons.add(cancelButton);
	buttons.setBorder(BorderFactory.createEmptyBorder(6, 0, 0, 0));
	
	states = new Stack();
	backButton.setEnabled(false);
	
	component = new JLabel();
	add(component, BorderLayout.CENTER);
	add(buttons, buttonPosition);
    }

    /**
       Invokes the current (initial) state.
     */
    public void start(State initialState) {
	if (initialState == null) {
	    throw new NullPointerException("Initial state may not be null");
	}
	states.push(initialState);
	initialState.stateEntered(this);	
    }
    
    /**
       Returns the finish button to allow adding listeners
       or to modify the look.
     */
    public JButton getFinishButton() {
	return finishButton;
    }

    public JButton getCancelButton() {
	return cancelButton;
    }

    public JButton getNextButton() {
	return nextButton;
    }
    
    public JButton getBackButton() {
	return backButton;
    }

    /**
       Sets the primary component.
     */
    public void setComponent(Component newComponent) {	
	if (newComponent != component) {
	    remove(component);
	    component = newComponent;
	    add(component, BorderLayout.CENTER);		    
	    repaint();
	}
    }

    /**
       Returns the stack of states that have been entered.
       The top state is the current state shown.
       @return the stack of states currently open.
     */
    public Stack getStates() {
	return states;
    }
    
    /**
       Returns the current state. This method is a convenience method
       and useful to quickly access the state the user finished with.
       @return the current state shown or the last state after finishing.
     */
    public State getCurrentState() {
	if (states == null) {
	    return null;
	}
	return (State)states.peek();
    }

    /**
       A state in the wizard dialog.
     */
    public interface State {

	/**
	   This method is called by the given wizard whenever the
	   state is entered (either by next or prev actions).  It
	   should initialize the user interface component to be shown
	   by the dialog (via Wizard.setComponent) and should also set
	   the transition rules by enabling/disabling the next
	   and finish buttons which are otherwise carried over. The
	   back button is handled automatically and the cancel button is
	   always active, but this behavior can be overridden. It
	   is up to the state implementation to cache the component
	   (for reentering), the wizard (for further queries) and to
	   possibly distinguish between first and subsequent entrances
	   (easily done using a flag).
	   @param parent the parent wizard that enters the state; the
	   parameter is for convenience only, it often is also the
	   outer object of this state.
	*/
	void stateEntered(Wizard parent);

	/**
	   This method is called by the parent wizard when the user
	   proceedes to the next state.  It should return the next
	   state.  This method may return arbitrary values
	   (<CODE>null</CODE>) if the proceeding transition has been
	   disabled.
	*/
	State nextState();
    }
    
}




