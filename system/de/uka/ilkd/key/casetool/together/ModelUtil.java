// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together;

import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.util.Debug;


public class ModelUtil {
    
    private ModelUtil() {}

   public static void hiliteMethod(Type t, ProgramMethod pm) {
      try{ 
	  ModelUtilImpl.hiliteMethod(t, pm);
      } catch(NoClassDefFoundError err) {
         System.err.println("Skipping Together part: hiliteMethod");
      } catch(RuntimeException re) {
	  System.err.println("Problem with method highlighting, enable debugging");
	  Debug.out(re);
      }
   }
}
