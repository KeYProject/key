/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse.resources.util;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;

public class KeY4EclipseResourcesUtil {
   
   
   public static KeYJavaType[] sortKeYJavaTypes(Set<KeYJavaType> kjts){
      Iterator<KeYJavaType> it = kjts.iterator();
      while (it.hasNext()) {
         KeYJavaType kjt = it.next();
         if (!(kjt.getJavaType() instanceof ClassDeclaration || 
               kjt.getJavaType() instanceof InterfaceDeclaration) || 
             ((TypeDeclaration)kjt.getJavaType()).isLibraryClass()) {
            it.remove();
         }
      }
      KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
      Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
         public int compare(KeYJavaType o1, KeYJavaType o2) {
            return o1.getFullName().compareTo(o2.getFullName());
         }
      });
      return kjtsarr;
   }
}