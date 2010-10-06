// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package aspects;

import java.awt.*;
import java.util.*;
import javax.swing.JComponent;

/** An aspect that tries to detect violations of the Swing
 * Single-Thread Rule.  It seems that the rule also applies to methods
 * in the model classes.  However, it is hard to find out for those
 * whether there is a visible component observing them.  So we just
 * say something about a `possible violation'.  Fortunately, there are
 * not so many of those.  Output goes as warnings and errors to the
 * key.aspects logger, so you usually need to set logging to WARN
 * level to see anything.
 */
public aspect CheckSwingThreadRule extends KeYAspect {

    pointcut threadSafeCalls()
        : call(void JComponent.revalidate())
        || call(void JComponent.invalidate())
        || call(void JComponent.repaint(..))
        || call(void add*Listener(EventListener+))
        || call(void remove*Listener(EventListener+));

    pointcut viewMethodCalls()
	: call(* javax..JComponent+.*(..));

    pointcut modelMethodCalls()
	: (   call(* javax..*Model+.*(..))
	      || call(* javax.swing.text.Document+.*(..)));

    pointcut uiMethodCalls()
	: viewMethodCalls() || modelMethodCalls();

    before(Object t) : uiMethodCalls() && 
	! threadSafeCalls() && target(t) &&
	if(!EventQueue.isDispatchThread()) {
	    // Don't complain for invisible components
	    if (t instanceof Component &&
		!((Component)t).isShowing()) {
		return;
	    }
	    String info = "Called method: "
		+ thisJoinPointStaticPart.getSignature()
		+ "\nCaller: "
		+ thisEnclosingJoinPointStaticPart.getSignature()
		+ "\nSource location: "
		+ thisJoinPointStaticPart.getSourceLocation()
		+ "\nThread: " + Thread.currentThread();
	    if (t instanceof Component) {
		Debug.log4jerror("Violation: Swing view method called"
				   +" from nonAWT thread for visible object\n"
				   + info,
				   "key.aspects");
	    } else {
		Debug.log4jwarn("Possible Violation: Model method" 
				  + " called from nonAWT thread\n"+info,
				  "key.aspects");
	    }
	}

}

