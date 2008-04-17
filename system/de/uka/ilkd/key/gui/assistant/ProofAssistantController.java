// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui.assistant;

import java.awt.Component;
import java.awt.Container;
import java.awt.event.*;
import java.util.LinkedList;
import java.util.List;

import javax.swing.AbstractButton;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.EventListenerList;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.configuration.GeneralSettings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * The proof assistant controller is connected to several system
 * points. The events send from these points are passed through to the
 * AI which decides about the actions to be executed.
 */
public class ProofAssistantController {

    /**
     * the mediator
     */
    private KeYMediator mediator;

    /**
     * the artificial intelligence to be informed about occured events
     */
    private ProofAssistantAI assistantAI; 

    /**
     * true if the assistant is activated
     */
    private boolean enabled;

    /**
     * true if the assistant is tentaive
     */
    private boolean registered;

    /** listens to events sent by the prover */
    private AIProofListener proofListener;
    
    /** listens to events sent by the toolbar */
    private AIToolBarListener toolBarListener;

    /** listens to events sent by the menu bar */
    private AIMenuBarListener menuBarListener;
    
    /** 
     * listens to events such as changing the selected node or proof
     */ 
    private AIKeYSelectionListener selectionListener;

    /** the frame object encapsulating the assistant pane */
    private ProofAssistant assistantGUI;

    /** 
     * list containing the listeners of the assistant 
     */
    private EventListenerList listeners = new EventListenerList();

    /** 
     * runnables to register the AI
     */
    private Runnable registerCtrl = new Runnable() {
	    public void run() {
		ProofAssistantController.this.register();
	    }
	};

    /** 
     * runnables to unregister the AI
     */
    private Runnable unregisterCtrl = new Runnable() {
	    public void run() {
		ProofAssistantController.this.unregister();
	    }
	};


    /**
     * creates the proof assistant controller associated with the
     * given AI.
     * @param mediator the KeYMediator
     * @param settings the GenberalSettings indicating if the
     * assistant should be enabled or disabled
     * @param ai the ProofAssistantAI
     * @param ui the ProofAssistant user interface
     */
    public ProofAssistantController(KeYMediator mediator,
				    GeneralSettings settings,
				    ProofAssistantAI ai, 
				    ProofAssistant ui) {
	
	this.mediator = mediator;
	settings.addSettingsListener(new AISettingsListener());
	assistantAI = ai;
	assistantGUI = ui;

	assistantGUI.addWindowListener
	    (new ProofAssistantWindowListener());
	
	init((Main)mediator.mainFrame());

	if (settings.proofAssistantMode()) {
	    enable();
	} else {
	    disable();
	}
    }


    /**
     * initialize the controller
     */
    private void init(Main mainFrame) {
	proofListener = new AIProofListener();
	selectionListener = new AIKeYSelectionListener();

	toolBarListener = new AIToolBarListener(mainFrame.getToolBar());
	mainFrame.getToolBar().addContainerListener(toolBarListener);

	menuBarListener = new AIMenuBarListener(mainFrame.getJMenuBar());
	mainFrame.getJMenuBar().addContainerListener(menuBarListener);

	final int width = mainFrame.getGraphicsConfiguration().
	    getDevice().getDisplayMode().getWidth();
	
	assistantGUI.setLocation(width-assistantGUI.getWidth(), 0);
    }

    /**
     * enables the assistant
     */
    public void enable() {
	if (enabled) return;
	if (!registered) register();
	// we have to register and stay registered as interactive
	// proof listener as long as AI is enabled
	registerAtInteractiveProver();
	assistantGUI.tearUp();
	enabled = true;
	fireStateChangeEvent();
    }

    /**
     * disables the assistant
     */
    public void disable() {
	if (!enabled) return;
	if (registered) unregister();
	unregisterAtInteractiveProver();
	assistantGUI.tearDown();
	enabled = false;
	fireStateChangeEvent();
    }

    /** 
     * Registers the controller at the interactive prover in
     * order. If in automatic application mode, we can unregister 
     * all listeners, but not the interactive prover
     * listener. Otherwise we would miss the event that the auto mode
     * has stopped, 
     */
    private void registerAtInteractiveProver() {
	mediator.addRuleAppListener(proofListener);
	mediator.addAutoModeListener(proofListener);
    }

    /** 
     * Registers the controller at the toolbar. The way this is done
     * is not nice at the moment, but we need a redesign of GUI to
     * realize it in a more convenient way.
     */
    private void registerAtToolBar() {
	toolBarListener.registerAll();
    }

    /** 
     * Registers the controller at the menubar. The way this is done
     * is not nice at the moment, but we need a redesign of GUI to
     * realize it in a more convenient way.
     */
    private void registerAtMenuBar() {
	menuBarListener.registerAll();	
    }

    /** 
     * Unregisters the controller at the interactive prover in
     * order. If in automatic application mode, we can unregister 
     * all listeners, but not the interactive prover
     * listener. Otherwise we would miss the event that the auto mode
     * has stopped, 
     */
    private void unregisterAtInteractiveProver() {
	mediator.removeRuleAppListener(proofListener);
	mediator.removeAutoModeListener(proofListener);
    }

    /** 
     * Unregisters the controller at the toolbar. 
     */
    private void unregisterAtToolBar() {
	toolBarListener.unregisterAll();
    }

    /** 
     * Unregisters the controller at the menubar. The way this is done
     * is not nice at the moment, but we need a redesign of GUI to
     * realize it in a more convenient way.
     */
    private void unregisterAtMenuBar() {
	menuBarListener.unregisterAll();
    }

    /**
     * registers at all observed system points
     */
    private void register() {
	if (registered) return;
	mediator.addKeYSelectionListener(selectionListener);
	registerAtToolBar();		
	registerAtMenuBar();
	registered = true;
    }

    /**
     * unregisters at all observed system points except at the
     * interactive prover
     */
    private void unregister() {
	if (!registered) return;
	mediator.removeKeYSelectionListener(selectionListener);
	unregisterAtToolBar();
	unregisterAtMenuBar();
	registered = false;
    }


    /** 
     * the given text is displayed by the assistant
     */
    public void displayText(String text) {
	if (assistantGUI != null) {
	    assistantGUI.setText(text);
	}
    }
    

    /**
     * returns the state of the assistant (true means enabled, false
     * disabled) 
     */
    public boolean getState() {
	return enabled;
    }


    /**
     * adds a change listener to this assistant 
     * @param l the ChangeListener
     */
    public void addChangeListener(ChangeListener l) {
	listeners.add(ChangeListener.class, l);
    }


    /**
     * removes the giben change listener from this assistant 
     * @param l the ChangeListener
     */
    public void removeChangeListener(ChangeListener l) {
	listeners.remove(ChangeListener.class, l);
    }

    /**
     * fire state change event
     */
    private void fireStateChangeEvent() {
	Object[] listenersArray = listeners.getListenerList();
	for (int i = listenersArray.length-2; i>=0; i-=2) {
	    if (listenersArray[i]==ChangeListener.class) {
		((ChangeListener)listenersArray[i+1]).stateChanged
		    (new ChangeEvent(this));
	    }
	}
    }

    // the window adapter to observer the GUI
    private class ProofAssistantWindowListener 
	extends WindowAdapter {

	public void windowClosing(WindowEvent we) {
	    ProofAssistantController.this.disable();	    
	}
	
    }


    // The different listeners connecting to the system points    

    /**
     * This abstract container listener can be subclassed if a
     * listener needs to be registered to all components of a
     * container. 
     */
    private abstract class AIContainerListener implements ContainerListener {

	private List<Component> components = new LinkedList<Component>();

	public abstract void register(Component c);
	public abstract void unregister(Component c);
	
	public AIContainerListener(Container container) {
	    init(container);
	}

	/**
	 * collects at all components of the given container and puts
	 * them in the observed list
	 */
	private void init(Container container) {
 	    Component[] comps = container.getComponents();
 	    for (int i = 0; i<comps.length; i++) {
		components.add(comps[i]);
	    }
	}

	/**
	 * registers at the added component and adds it to the list of
	 * observed components
	 */
	public void componentAdded(ContainerEvent ce) {
	    register(ce.getChild());
	    components.add(ce.getChild());
	}

	/**
	 * unregisters at the added component and removes it from the list of
	 * observed components
	 */
	public void componentRemoved(ContainerEvent ce) {
	    unregister(ce.getChild());
	    components.remove(ce.getChild());
	}


	/**
	 * registers all observed components
	 */
	public void registerAll() {
	    synchronized(components) {
                for (final Component c : components) {
		    register(c);
		}
	    }
	}

	/**
	 * unregisters all observed components, but keeps them in the
	 * observed component list
	 */
	public void unregisterAll() {
	    synchronized(components) {
                for (final Component c : components) {
		    unregister(c);
		}
	    }
	}

    }

    /**
     * This listener listens to toolbar events. %%%
     * The GUI needs to be redesigned then the implementation of this
     * listener could be nicer, but in the meantime.
     */
    private class AIToolBarListener extends AIContainerListener
	implements ActionListener {
	
	private ProofAssistantController ctrl = ProofAssistantController.this;

	public AIToolBarListener(Container container) {
	    super(container);
	}

	public void actionPerformed(ActionEvent e) {
	    if (e.getSource() instanceof AbstractButton) {
		ctrl.assistantAI.analyze
		    (new PressedButtonEventInput
		     ((AbstractButton)e.getSource(), 
		     AIInput.TOOLBAR_EVENT)).execute(ctrl);
	    }
	}

	public void register(Component c) {
	    if (c instanceof AbstractButton) {
		((AbstractButton)c).addActionListener(this);
	    }
	}

	public void unregister(Component c) {
	    if (c instanceof AbstractButton) {
		((AbstractButton)c).removeActionListener(this);
	    }
	}	
    }

    /**
     * This listener listens to menubar events. %%%
     * The GUI needs to be redesigned then the implementation of this
     * listener could be nicer, but in the meantime.
     */
    private class AIMenuBarListener extends AIContainerListener 
	implements ItemListener {
	
	private ProofAssistantController ctrl = ProofAssistantController.this;

	public AIMenuBarListener(Container container) {
	    super(container);
	}

	public void itemStateChanged(ItemEvent e) {
	    if (e.getStateChange() == ItemEvent.SELECTED) {
		ctrl.assistantAI.analyze
		    (new PressedButtonEventInput
		     ((AbstractButton)e.getSource(), 
		      AIInput.MENUBAR_EVENT)).execute(ctrl);	    
	    }
	}

	public void register(Component c) {
	    if (c instanceof AbstractButton) {
		((AbstractButton)c).addItemListener(this);
	    }
	}

	public void unregister(Component c) {
	    if (c instanceof AbstractButton) {
		((AbstractButton)c).removeItemListener(this);
	    }
	}	
    }

    /**
     * This listener reacts on proof events
     */
    private class AIProofListener implements RuleAppListener,
                                             AutoModeListener {
	
	private ProofAssistantController ctrl = ProofAssistantController.this;
	private boolean attentive = true;
	
	/** 
	 * invoked if automatic execution has started
	 */
	public void autoModeStarted(ProofEvent e) {
	    new Thread(unregisterCtrl).start();
	    attentive = false;
	}
	
	/** 
	 * invoked if automatic execution has stopped
	 */
	public void autoModeStopped(ProofEvent e) {
	    new Thread(registerCtrl).start();
	    attentive = true;
	}
	
	/** 
	 * invoked when a rule has been applied 
	 */
	public void ruleApplied(ProofEvent e) {
	    if (enabled && attentive) {
		if (e.getRuleAppInfo() != null) {
		    RuleApp appliedRule = 
			e.getRuleAppInfo().getRuleApp();		
		    ctrl.assistantAI.analyze
			(new RuleEventInput(appliedRule)).execute(ctrl);
		}
	    }
	}
    }

    
    private class AIKeYSelectionListener 
	implements KeYSelectionListener {

	/** focused node has changed */
	public void selectedNodeChanged(KeYSelectionEvent e) {
	}
	
	/** 
	 * the selected proof has changed 
	 * (e.g. a new proof has been loaded) 
	 */ 
	public void selectedProofChanged(KeYSelectionEvent e) {	    
	    if (enabled) {
		if (registered) {
		    new Thread(unregisterCtrl).start();
		}
		new Thread(registerCtrl).start();	    
	    }
	} 
    }


    private class AISettingsListener implements SettingsListener {

	/** 
	 * called by the Settings object to inform the listener that its
	 * state has changed
	 * @param e the Event sent to the listener
	 */
	public void settingsChanged(GUIEvent e) {
	    if (e.getSource() instanceof GeneralSettings) {
		GeneralSettings gSet = (GeneralSettings) e.getSource();
		if (gSet.proofAssistantMode() != 
		    ProofAssistantController.this.enabled) {
		    if (enabled) {
			ProofAssistantController.this.disable();
		    } else {
			ProofAssistantController.this.enable();
		    }
		}
	    }
	}
    }
    

}
