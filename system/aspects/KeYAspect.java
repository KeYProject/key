// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package aspects;

/** The abstract super-aspect for all aspects compiled into
 * the KeY system.  It takes care of registering aspects with
 * the compiledAspects method of the Main class.
 *
 */

public abstract aspect KeYAspect {

      String around() : 
	  execution(String de.uka.ilkd.key.gui.Main.compiledAspects()) {
  	return (getClass().getName())+"\n" + proceed();
      }

}
