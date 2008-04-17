// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.proof.reuse;

import java.io.*;
import java.util.Iterator;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.parser.diffparser.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public class ReuseFrontend {

   private KeYMediator mediator;
   LineNumberReader r;

   public ReuseFrontend(KeYMediator medi) {
      this.mediator = medi;
   }
   
   public String markup(Proof source, File diffFile) {
      try {
         return markup(source, new LineNumberReader(new FileReader(diffFile)));
      } catch (IOException ioe) {
         return ioe.toString();
      }
   }


   public String markup(Proof source, String s) {
      return markup(source, new LineNumberReader(new StringReader(s)));
   }


   public String markup(Proof source, LineNumberReader r) {
      try {
         DiffParserTokenManager lexer = new DiffParserTokenManager(
            new SimpleCharStream(r), DiffParserConstants.LINE_BEGIN);
         DiffParser p = new DiffParser(lexer);
         p.UniDiff();
         DiffParser.MarkerHint[] hints;
         hints = p.getMarkers();
         for (int i=0; i<hints.length; i++) {
            Logger.getLogger("key.proof.mgt").debug(
	       "Markup hint: "+  hints[i].file+":"+ hints[i].line); 
            recMark(source.root(), hints[i]);
         }
         markRoot(source);
         
         return null;
      } catch (ParseException e) {
         return e.toString();
      } catch (TokenMgrError er) {
         return er.toString();
      }
   }
   
   public void markRoot(Proof source)  {
      mediator.markPersistent(source.root());
   }
   
   
   private void recMark(Node n, DiffParser.MarkerHint hint) {
      if (("/"+hint.file).equals(n.getNodeInfo().getExecStatementParentClass())) {
         int line = n.getNodeInfo().getExecStatementPosition().getLine();
         if (line >= hint.line) {
            mediator.markPersistent(n);
            return;
         }
      }
      
      final Iterator<Node> ch = n.childrenIterator();
      while (ch.hasNext()) { 
          recMark(ch.next(), hint);
      }
   }
   
   

}
