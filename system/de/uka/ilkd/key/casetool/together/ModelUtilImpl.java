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

import com.togethersoft.openapi.ide.IdeAccess;
import com.togethersoft.openapi.ide.diagram.IdeDiagram;
import com.togethersoft.openapi.ide.diagram.IdeDiagramElement;
import com.togethersoft.openapi.ide.diagram.IdeDiagramManager;
import com.togethersoft.openapi.rwi.RwiDiagram;
import com.togethersoft.openapi.rwi.RwiElement;
import com.togethersoft.openapi.rwi.RwiModel;
import com.togethersoft.openapi.rwi.RwiModelAccess;
import com.togethersoft.openapi.sci.*;

import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.op.ProgramMethod;

class ModelUtilImpl {

    private ModelUtilImpl() {}

    /**
     * Get the method signature in Together format
     * e.g.: callM#(#SuperA#C#)#
     * @author VK
     */
    static String togetherSignature(ProgramMethod pm) {
       String s = pm.name().toString()+"#(#";
       for (int i=0; i<pm.arity()-1; i++) {
          if (i>0) s = s+"#";
          s = s+pm.getMethodDeclaration().getParameterDeclarationAt(i).
                     getVariableSpecification().
                     getType().
                     getFullName();
       }
       s = s + "#)#";
       return s;
    }
    
   static void hiliteMethod(Type t, ProgramMethod pm) {
      SciModel sciModel = SciModelAccess.getModel(); 
      RwiModel rwiModel = RwiModelAccess.getModel(); 


      SciClass cl = sciModel.findClass(SciLanguage.JAVA,t.getFullName());      
      SciMember op = SciUtil.findMemberBySignature(cl, togetherSignature(pm), 
                                                   true);

//      SciOperationEnumeration openum = cl.operations();
//      while (openum.hasMoreElements())
//         System.out.println(openum.nextSciOperation().getSignature());
//      System.out.println("op="+op);


      RwiElement rwiOp = rwiModel.findMember(op);

      IdeDiagramManager diaMan = IdeAccess.getDiagramManager();
      RwiDiagram rwiDiagram2 = rwiModel.findDiagramFor(rwiOp);
      IdeDiagram dia = diaMan.openDiagram(rwiDiagram2, true);
      diaMan.setActiveDiagram(dia);
      IdeDiagramElement idx = dia.findElement(rwiOp);
//      System.out.println(idx);
      dia.unselectAll();
      dia.select(idx);
   }

}


