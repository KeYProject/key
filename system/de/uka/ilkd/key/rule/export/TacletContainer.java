/*
 * Created on 07.12.2004
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package de.uka.ilkd.key.rule.export;

import de.uka.ilkd.key.logic.Named;

/**
 * @author stenger
 *
 * This interface generalizes the concept of a named set of taclets,
 * like a rule set, a .key file, etc.
 */
public interface TacletContainer extends Named {
    ListOfTacletModelInfo getTaclets ();
}
